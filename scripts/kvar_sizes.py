#!/usr/bin/env python3
"""Report the relative line sizes of KVar entries in a .fqout file."""

import argparse
import re


KVAR_HEADER = re.compile(r"^(\$[^\s\[]+)\[")


def read_entries(path):
    entries = []
    section = "solution"
    current = None

    with open(path, encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if line.strip() == "Non-cut kvars:":
                section = "non-cut"

            match = KVAR_HEADER.match(line)
            if match:
                if current is not None:
                    current["end"] = line_number - 1
                    current["lines"] = current["end"] - current["start"] + 1
                    entries.append(current)
                current = {
                    "name": match.group(1),
                    "kind": section,
                    "start": line_number,
                }

        if current is not None:
            current["end"] = line_number
            current["lines"] = current["end"] - current["start"] + 1
            entries.append(current)

    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fqout", help="path to a .fqout file")
    args = parser.parse_args()

    entries = read_entries(args.fqout)
    total = sum(entry["lines"] for entry in entries)

    print(f"{'KVar':<8} {'Kind':<8} {'Lines':>10} {'Percent':>9} {'Range':>15}")
    print("-" * 56)
    for entry in sorted(entries, key=lambda item: item["lines"], reverse=True):
        percent = 100.0 * entry["lines"] / total if total else 0.0
        line_range = f"{entry['start']}-{entry['end']}"
        print(
            f"{entry['name']:<8} {entry['kind']:<8} "
            f"{entry['lines']:>10} {percent:>8.2f}% {line_range:>15}"
        )
    print("-" * 56)
    print(f"{'Total':<8} {'':<8} {total:>10}")


if __name__ == "__main__":
    main()
