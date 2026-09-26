#!/usr/bin/env python3
"""Extract Overture Places rows for given US states and write a compact parquet.

Runs on GitHub Actions runners (clean egress to S3) so the Storm Fix Now VM
(which cannot reach S3) can still get fresh Overture data. The VM dispatches
the `overture-extract` workflow, then downloads the parquet via the workflow
artifact API.

Usage:
    python overture_extract.py --release 2026-09-23.1 --states AZ,ND,SD \
        --out /tmp/overture_extract.parquet

The SELECT mirrors stormfix.business_data.overture_import.remote_overture_query
so the VM-side importer can consume the parquet with the same normalization.
"""

from __future__ import annotations

import argparse
import sys
import time


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--release", required=True, help="Overture release, e.g. 2026-09-23.1")
    parser.add_argument("--states", required=True, help="Comma-separated US state codes")
    parser.add_argument("--out", required=True, help="Output parquet path")
    args = parser.parse_args()

    states = sorted({s.strip().upper() for s in args.states.split(",") if s.strip()})
    if not states:
        print("no states given", flush=True)
        return 1

    import duckdb

    path = (
        f"s3://overturemaps-us-west-2/release/{args.release}/theme=places/type=place/*"
    )
    conn = duckdb.connect()
    conn.execute("INSTALL httpfs")
    conn.execute("LOAD httpfs")
    conn.execute("SET s3_region='us-west-2'")

    # Fail fast with a clear message if the release path does not exist.
    files = conn.execute("SELECT count(*) FROM glob(?)", [path]).fetchone()
    print(f"release path glob matched {files[0]} files", flush=True)
    if not files[0]:
        print(f"ERROR: no files at {path}; check the release string", flush=True)
        return 2

    quoted = ", ".join(f"'{s}'" for s in states)
    # Schema v2.0.0 (release >= 2026-09-23) removed `categories`; use
    # `taxonomy` + top-level `basic_category` instead. String comparison
    # works because releases are YYYY-MM-DD suffixed.
    is_v2 = args.release >= "2026-09-23"
    cat_cols = "taxonomy, basic_category" if is_v2 else "categories"
    sql = f"""
        SELECT
            id,
            names,
            {cat_cols},
            confidence,
            websites,
            emails,
            phones,
            addresses,
            bbox.ymin AS latitude,
            bbox.xmin AS longitude
        FROM read_parquet(?, filename=true, hive_partitioning=1)
        WHERE addresses[1].country = 'US'
          AND upper(addresses[1].region) IN ({quoted})
    """
    started = time.time()
    # Probe: log the actual column types so the VM side can adapt.
    probe = conn.execute(
        f"SELECT {cat_cols} FROM read_parquet(?) LIMIT 1", [path]
    )
    print("column types:", probe.description, flush=True)
    sample = probe.fetchone()
    print("sample:", str(sample)[:500], flush=True)
    # Stream straight to parquet; no giant in-memory frame.
    conn.execute(f"COPY ({sql}) TO ? (FORMAT PARQUET)", [path, args.out])
    elapsed = time.time() - started

    n = conn.execute("SELECT count(*) FROM read_parquet(?)", [args.out]).fetchone()[0]
    with_email = conn.execute(
        "SELECT count(*) FROM read_parquet(?) WHERE len(emails) > 0", [args.out]
    ).fetchone()[0]
    with_website = conn.execute(
        "SELECT count(*) FROM read_parquet(?) WHERE len(websites) > 0", [args.out]
    ).fetchone()[0]
    print(
        f"done: {n} rows, {with_email} with email "
        f"({100.0 * with_email / max(n, 1):.1f}%), "
        f"{with_website} with website ({100.0 * with_website / max(n, 1):.1f}%) "
        f"in {elapsed:.1f}s",
        flush=True,
    )

    # Write a stats JSON for the VM to fetch via raw.githubusercontent.com
    # (workflow artifacts live on blocked blob storage).
    stats = {
        "extract_id": args.out.replace("overture_", "").replace(".parquet", ""),
        "release": args.release,
        "states": states,
        "total": n,
        "with_email": with_email,
        "with_website": with_website,
        "email_pct": round(100.0 * with_email / max(n, 1), 2),
        "website_pct": round(100.0 * with_website / max(n, 1), 2),
        "by_state": {},
        "taxonomy_sample": [],
    }
    for row in conn.execute(
        """
        SELECT addresses[1].region AS st, count(*) AS n,
               sum(CASE WHEN len(emails) > 0 THEN 1 ELSE 0 END) AS e,
               sum(CASE WHEN len(websites) > 0 THEN 1 ELSE 0 END) AS w
        FROM read_parquet(?)
        GROUP BY st ORDER BY n DESC
        """,
        [args.out],
    ).fetchall():
        stats["by_state"][row[0]] = {
            "total": row[1],
            "email": row[2],
            "website": row[3],
        }
    if is_v2:
        for row in conn.execute(
            "SELECT to_json(taxonomy), basic_category FROM read_parquet(?) LIMIT 10",
            [args.out],
        ).fetchall():
            stats["taxonomy_sample"].append(
                {"taxonomy": str(row[0])[:300], "basic_category": str(row[1])}
            )
    stats_path = args.out.replace(".parquet", ".stats.json")
    import json as _json

    with open(stats_path, "w") as fh:
        _json.dump(stats, fh, indent=2)
    print(f"wrote stats to {stats_path}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
