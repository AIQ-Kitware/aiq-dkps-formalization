#!/usr/bin/env python3
"""Small *direct* invocation of LeanExplore's documented local Service API.

No remote client, MCP proxy, common schema or new index. JSON returns the
native SearchResponse, preserving names, source and package metadata.
"""
import argparse
import asyncio
import json
import sys


def parse_args():
    parser = argparse.ArgumentParser(description="Query the locally installed LeanExplore Service")
    parser.add_argument("query", help="Natural-language or Lean expression query")
    parser.add_argument("--limit", type=int, default=10)
    parser.add_argument("--rerank-top", type=int, default=25, help="0 disables reranking")
    parser.add_argument("--package", action="append", default=[], help="Repeat for multiple packages")
    parser.add_argument("--json", action="store_true", help="Emit native SearchResponse JSON")
    return parser.parse_args()


async def search(args):
    from lean_explore.search import Service

    service = Service()
    return await service.search(
        query=args.query,
        limit=args.limit,
        rerank_top=args.rerank_top,
        packages=args.package or None,
    )


def main():
    args = parse_args()
    if args.limit < 1 or args.rerank_top < 0:
        raise SystemExit("--limit must be positive and --rerank-top must be >=0")
    try:
        result = asyncio.run(search(args))
    except Exception as exc:
        print(f"LeanExplore local search failed: {exc}", file=sys.stderr)
        print("Check install-leanexplore.sh --fetch-assets and local model caches.", file=sys.stderr)
        return 1
    if args.json:
        print(result.model_dump_json(indent=2))
        return 0
    print(f"{result.count} results ({result.processing_time_ms} ms)")
    for n, item in enumerate(result.results, start=1):
        print(f"{n:3}. {item.name}  [{item.module}]")
        description = item.docstring or item.informalization or ""
        if description:
            print("     " + " ".join(description.split())[:260])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
