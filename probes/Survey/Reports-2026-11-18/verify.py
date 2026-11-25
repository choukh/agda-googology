"""从附件恢复 W4 及指定批次，在新目录逐项检查。用 --library-file 指定 Agda 库表。"""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def restore(survey, work, batch):
    archive = survey / "Reports-2026-11-16" / "attachments"
    for group in ("B4W4", "B5D", "B6A", "B7A", "B8A", "B8N", "B9A", "B9N",
                  "B10A", "B10B", "B10Join", "B11A", "B11B", "B11Join"):
        for source in sorted(archive.glob(group + "-*.agda.txt")):
            name = source.name.removeprefix(group + "-").removesuffix(".txt")
            (work / name).write_bytes(source.read_bytes())

    lead = survey / "Lead"
    code = re.findall(r"(?ms)^```agda\n(.*?)^```$", (lead / "指令-01.md").read_text())
    modules = [re.search(r"(?m)^module (\w+) where$", part)[1] for part in code]
    assert modules == ["YiLAB7Orbit", "YiLAB7Replay"], modules
    for name, part in zip(modules, code):
        (work / (name + ".agda")).write_text(part)
    for source in (lead / "attachments").glob("YiLAB*.agda.txt"):
        (work / source.name.removesuffix(".txt")).write_bytes(source.read_bytes())
    if batch >= 20:
        source = lead / "attachments" / "YiLAStatusFGH.agda.txt"
        (work / source.name.removesuffix(".txt")).write_bytes(source.read_bytes())

    new = []
    sources = list((survey / "Reports-2026-11-18" / "attachments").glob("B*.agda.txt"))
    if batch >= 23:
        sources.extend((survey / "Reports-2026-11-19" / "attachments").glob("B*.agda.txt"))
    if batch >= 25:
        for source in (survey / "Reports-2026-11-19" / "attachments").glob("QBtbo*.agda.txt"):
            (work / source.name.removesuffix(".txt")).write_bytes(source.read_bytes())
    for source in sorted(sources):
        number = int(re.match(r"B(\d+)", source.name)[1])
        if number > batch:
            continue
        target = work / source.name.removesuffix(".txt")
        target.write_bytes(source.read_bytes())
        if number == batch:
            new.append(target.stem)
    return new


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library-file", type=Path, required=True)
    parser.add_argument("--batch", choices=range(12, 32), type=int, default=12)
    parser.add_argument("modules", nargs="*", help="只检查指定入口；默认检查全部附件")
    args = parser.parse_args()
    survey = Path(__file__).resolve().parent.parent
    root = survey.parent.parent
    work = Path(tempfile.mkdtemp(prefix=f"agda-w4-b{args.batch}-")).resolve()
    print(work, flush=True)
    modules = restore(survey, work, args.batch)
    first = ["B11Join", "B11OuterMain", "B12StrictExit", "B12Omega", "B12TerminalSrc"]
    if args.batch == 13:
        first = ["B13FiniteClosed", "B13LiveRow", "B13FiniteGap", "B13FiniteNeg", "B13SharpOne"]
    elif args.batch == 14:
        first = ["B14LiveTower", "B14Goal", "B14SharpStation", "B14SharpOffset", "B14SharpNext"]
    elif args.batch == 15:
        first = ["B15Join", "B15OriginalTail", "B15RefSource", "B15RefGain",
                 "B15SharpTail", "B15SharpRank"]
    elif args.batch == 16:
        first = ["B16Closed", "B16GammaRows", "B16OrbitAgain", "B16SharpSource",
                 "B16SharpTerminal"]
    elif args.batch == 17:
        first = ["B16Closed", "B16SharpSource", "B17RefAllSource", "B17RefSwap",
                 "B17OrbitFour", "B17OrbitThree", "B17Join", "B17SharpSelected",
                 "B17SharpThree", "B17Legacy", "B17ActualSlots", "B17TowerRules",
                 "B17Calibration", "B17CellPrefix", "B17CapFirst", "B17Single",
                 "B17CellNext"]
    elif args.batch >= 18:
        first = ["B16Closed", "B16GammaRows", "B16SharpSource", "B17OrbitFour",
                 "B17OrbitRow", "B17SharpThree", "B17Legacy", "B17CellNext",
                 "B17Single", "B18OrbitRows", "B18SharpGain", "B18SharpShape",
                 "B18RefProduct", "B18ResetCellGoal", "B18OldBridge",
                 "B18History", "B18RefIdeal"]
        if args.batch >= 19:
            first += ["B19PathShape", "B19Coefficient", "B19Canonical", "B19FirstTower",
                      "B19OldNodes", "B19RowSingle", "B19RowNode", "B19IdealGamma",
                      "B19IdealSelected", "B19RowSecondParent", "B19RowReset",
                      "B19IdealThreshold", "B19PhysicalCut", "B19OldTrace",
                      "B19OldFinite", "B19OldFeedback", "B19OldPowers"]
        if args.batch >= 20:
            first += ["B20HeadActual", "B20TowerValues", "B20SeriesShape",
                      "B20SlotTail", "B20StandardInside", "B20StandardGoal",
                      "B20OldSecond", "B20OldSource", "B20OldAddress", "B20StandardSource",
                      "B20OldRoom", "B20RowIndex", "B20IdealSource", "B20IdealPhysical",
                      "B20OldRanks", "B20OldBlocks", "B20RowAcross", "B20RowBound",
                      "B20UnitSecond", "B20UnitCells", "B20IdealRetained", "B20IdealOldCut"]
        if args.batch >= 21:
            first += ["B21TowerWords", "B21TowerRead", "B21FirstDiagonal",
                      "B21RowWhole", "B21RowRepeat", "B21RowX2",
                      "B21IdealNode", "B21IdealCarry", "B21IdealInside",
                      "B21CrossAll", "B21CrossSource", "B21CrossCoefficient",
                      "B21CrossCut", "B21RowSource"]
        if args.batch >= 22:
            first += ["B22RowSource", "B22RowBoundary", "B22RowVariable",
                      "B22TowerDiagonal", "B22TowerCut", "B22TowerPorts",
                      "B22CrossTest", "B22CrossCount", "B22CrossRead",
                      "B22IdealOld", "B22IdealTest"]
    if args.batch == 23:
        first = ["B23LJoined", "B23RFamily", "B23RControl", "B23ASelected",
                 "B23NCut", "B23LSupport", "B23AReach", "B23RCut"]
    if args.batch == 24:
        first = ["B12Terminal", "B18OrbitRows", "B21RowTheta", "B22RowVariable",
                 "B23ABlocks", "B23RExit", "B24AClosed", "B24AQueries", "B24NStore", "B24RCompare"]
    if args.batch >= 25:
        first = ["B12Terminal", "B18OrbitRows", "B21RowTheta", "B22RowVariable",
                 "B23ABlocks", "B23RExit", "B24AClosed", "B24NStore",
                 "B25DLimit", "B25PoolFirst", "B25FReturn", "B25FFloor",
                 "B25ASource", "B25ScalarLimit"]
    if args.batch >= 26:
        first += ["B26OSection", "B26OExact", "B26Depth", "B26CJump",
                  "B26PFactor", "B26PInterval", "B26CActual", "B26CCompare",
                  "B26CCardinal", "B26Boundary", "B26Profile", "B26Transport",
                  "B26BoundedSyntax", "B26Flat", "B26CMeaning", "B26OUContext",
                  "B26OUValue", "B26OUActual", "B26OUUnit"]
    if args.batch >= 27:
        # 逐件装入本批依赖，使联合入口也能在单工 6G 内复现。
        from graphlib import TopologicalSorter
        for number in range(27, args.batch + 1):
            prefix = f"B{number}"
            imports = rf"(?m)^\s*(?:open )?import ({prefix}\w+)\b"
            dependencies = {
                source.stem: sorted(set(re.findall(imports, source.read_text())))
                for source in sorted(work.glob(prefix + "*.agda"))
            }
            first.extend(TopologicalSorter(dependencies).static_order())
    entries = args.modules or first + [m for m in modules if m not in first]
    seen = set()
    for name in entries:
        if name in seen:
            continue
        source = work / (name + ".agda")
        if not source.is_file():
            raise SystemExit("缺源码 " + name)
        command = ["agda", "+RTS", "-M6G", "-RTS", "--library-file=" + str(args.library_file.resolve()),
                   "-W", "noUnsupportedIndexedMatch", "-i", "src", "-i", "probes",
                   "-i", str(work), "--dependency-graph=" + str(work / (name + ".dot")), str(source)]
        log = work / (name + ".log")
        with log.open("w") as out:
            run = subprocess.run(command, cwd=root, stdout=out, stderr=subprocess.STDOUT)
        output = log.read_text()
        names = set(re.findall(r"(?m)^\s*Checking ([\w.]+) \(", output))
        print(name, "exit", run.returncode, "Checking", len(names), flush=True)
        if run.returncode or name not in names:
            print(output[-2000:])
            raise SystemExit(run.returncode or 1)
        seen.update(names)
    if not args.modules and not set(modules) <= seen:
        raise SystemExit("缺 Checking 行 " + str(set(modules) - seen))


if __name__ == "__main__":
    main()
