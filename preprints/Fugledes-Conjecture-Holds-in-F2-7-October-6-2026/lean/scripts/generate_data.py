"""Generate Lean certificate data from the computational verification package."""

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT.parent / "verification"


def linear_combination(rows, coefficients):
    result = 0
    for index, row in enumerate(rows):
        if coefficients >> index & 1:
            result ^= row
    return result


def coordinates(rows, target):
    """Express target as an XOR of rows, returning the coefficient bit mask."""
    pivots = {}
    for index, row in enumerate(rows):
        value, mask = row, 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = value, mask
                break
            previous, previous_mask = pivots[pivot]
            value ^= previous
            mask ^= previous_mask

    value, mask = target, 0
    while value:
        pivot = value.bit_length() - 1
        if pivot not in pivots:
            raise ValueError("A coordinate witness is outside the source row space.")
        previous, previous_mask = pivots[pivot]
        value ^= previous
        mask ^= previous_mask
    if linear_combination(rows, mask) != target:
        raise ValueError("Incorrect linear-combination witness.")
    return mask


def transpose(rows):
    n = len(rows)
    return [sum(((rows[i] >> j) & 1) << i for i in range(n)) for j in range(n)]


def dephase(rows):
    n = len(rows)
    return [row ^ rows[0] ^ (((row ^ rows[0]) & 1) * ((1 << n) - 1)) for row in rows]


def format_list(values, indent=2, hexadecimal=False):
    digits = max(((value.bit_length() + 3) // 4 for value in values), default=1)
    words = [f"0x{value:0{digits}x}" if hexadecimal else str(value) for value in values]
    single_line = "[" + ", ".join(words) + "]"
    prefix = " " * indent
    if len(single_line) + indent <= 92:
        return prefix + single_line
    width = 4 if hexadecimal else 8
    chunks = [", ".join(words[i:i + width]) for i in range(0, len(words), width)]
    return prefix + "[" + (",\n" + prefix + " ").join(chunks) + "]"


def format_field(name, values):
    rendered = format_list(values, indent=4)
    single_line = f"  {name} := {rendered.strip()}"
    if "\n" not in rendered and len(single_line) <= 92:
        return [single_line]
    return [f"  {name} :=", rendered]


def source_matrices():
    sources = {}
    for index in range(5):
        filename = INPUT / f"had.16.{index}.txt"
        lines = [line.strip() for line in filename.read_text(encoding="utf-8").splitlines()]
        lines = [line for line in lines if len(line) == 16 and set(line) <= {"+", "-"}]
        if len(lines) != 16:
            raise ValueError(f"Expected 16 rows in {filename.name}.")
        sources[16, index] = [sum((sign == "+") << j for j, sign in enumerate(line))
                              for line in lines]
    for line in (INPUT / "had32_rank_le7.txt").read_text(encoding="utf-8").splitlines():
        fields = line.split()
        index = int(fields[0])
        if len(fields) != 34 or (32, index) in sources:
            raise ValueError("Invalid order-32 representative.")
        sources[32, index] = [int(word, 16) for word in fields[2:]]
    if len(sources) != 21:
        raise ValueError("Expected five order-16 and sixteen order-32 representatives.")
    return sources


def certificate_definitions(sources, order, records):
    definitions, cases = [], []
    for record in records:
        index = record["index"] if order == 16 else record["class_index"]
        transposed = record.get("transpose", False)
        label = f"order{order}_{index}" + ("_transpose" if transposed else "")
        rows = transpose(sources[order, index]) if transposed else sources[order, index]
        logarithmic_rows = dephase(rows)
        basis = [sum(((point >> k) & 1) << j for j, point in enumerate(record["E"]))
                 for k in range(record["r"])]
        fields = {
            "points": record["E"],
            "complement": record["T"],
            "rowCoordinates": [coordinates(basis, row) for row in logarithmic_rows],
            "basisSourceMasks": [coordinates(logarithmic_rows, row) for row in basis],
        }
        definitions.extend([f"def {label} : Certificate where", f"  rank := {record['r']}"])
        for field, values in fields.items():
            definitions.extend(format_field(field, values))
        definitions.append("")
        cases.extend([
            f"    {{ order := {order}, classIndex := {index}, transposed := {str(transposed).lower()},",
            f"      source := source{order}_{index}, certificate := {label} }},",
        ])
    return definitions, cases


def hadamard_data():
    sources = source_matrices()
    records16 = json.loads((INPUT / "spectral16_certificates.json").read_text(encoding="utf-8"))
    records32 = json.loads((INPUT / "spectral32_certificates.json").read_text(encoding="utf-8"))
    if len(records16) != 5 or {record["index"] for record in records16} != set(range(5)):
        raise ValueError("Expected the five order-16 certificates.")
    orientations = {(index, transposed) for n, index in sources if n == 32
                    for transposed in (False, True)}
    if len(records32) != 32 or {(record["class_index"], record["transpose"])
                              for record in records32} != orientations:
        raise ValueError("Expected both orientations of each order-32 representative.")

    lines = ["import FugledeCertificates.Definitions", "",
             "-- Generated from ../verification/ by scripts/generate_data.py.", "",
             "namespace FugledeCertificates.Data", ""]
    for (order, index), rows in sorted(sources.items()):
        lines.extend([f"def source{order}_{index} : List Nat :=",
                      format_list(rows, hexadecimal=True), ""])
    for order, records in ((16, records16), (32, records32)):
        definitions, cases = certificate_definitions(sources, order, records)
        lines.extend(definitions)
        lines.extend([f"def order{order}Certificates : List HadamardCase :=", "  ["])
        cases[-1] = cases[-1].rstrip(",")
        lines.extend(cases)
        lines.extend(["  ]", ""])
    lines.extend(["end FugledeCertificates.Data", ""])
    return "\n".join(lines)


def eight_point_data():
    records = json.loads((INPUT / "eight_certificates.json").read_text(encoding="utf-8"))
    positive = [(index, record) for index, record in enumerate(records)
                if record["tile"] is not None]
    if len(records) != 549 or len(positive) != 168:
        raise ValueError("Expected 168 positive certificates among 549 eight-point records.")
    lines = ["import FugledeCertificates.Spectrum", "",
             "-- Generated from ../verification/eight_certificates.json.",
             "-- Definition suffixes are zero-based record indices.", "",
             "namespace FugledeCertificates.Data", ""]
    for index, record in positive:
        lines.extend([f"def eight_{index} : EightCertificate where", f"  rank := {record['r']}"])
        for field, original in (("points", "T"), ("complement", "tile"),
                                ("spectrum", "spectrum"), ("universalFrequencies", "universal")):
            lines.extend(format_field(field, record[original]))
        lines.append("")
    names = [f"eight_{index}" for index, _ in positive]
    lines.extend(["def eightPointCertificates : List EightCertificate :=", "  ["])
    for offset in range(0, len(names), 6):
        suffix = "," if offset + 6 < len(names) else ""
        lines.append("    " + ", ".join(names[offset:offset + 6]) + suffix)
    lines.extend(["  ]", "", "end FugledeCertificates.Data", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check data without rewriting files")
    args = parser.parse_args()
    outputs = {ROOT / "FugledeCertificates/Data/Hadamard.lean": hadamard_data(),
               ROOT / "FugledeCertificates/Data/EightPoint.lean": eight_point_data()}
    for filename, content in outputs.items():
        if args.check:
            if not filename.is_file() or filename.read_bytes() != content.encode("utf-8"):
                raise SystemExit(f"Generated data differ: {filename.relative_to(ROOT)}")
        else:
            filename.parent.mkdir(parents=True, exist_ok=True)
            filename.write_text(content, encoding="utf-8", newline="\n")
    print("Certificate data match the original inputs." if args.check else "Generated certificate data.")


if __name__ == "__main__":
    main()
