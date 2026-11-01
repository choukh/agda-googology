#!/usr/bin/env bash
# 重取 src/Mahlo 用到的全部文献（PDF 不入库）。用法：bash FETCH.sh
set -u
cd "$(dirname "$0")"
get() { curl -sL -m 90 -A "Mozilla/5.0" -o "$2" "$1" && printf '%-32s %s\n' "$2" "$(file -b --mime-type "$2")"; }
get https://csetzer.github.io/articles/mahlo.pdf                               setzer2000-mahlo.pdf
get https://csetzer.github.io/articles/modeltypetheoryinaccessiblemahlo.pdf    setzer-partI.pdf
get https://csetzer.github.io/articles/1papdiss.pdf                            setzer1996-uppermahlo.pdf
get https://csetzer.github.io/articles/2papdiss.pdf                            setzer1998-wellordering.pdf
get https://csetzer.github.io/articles/weor0.pdf                               setzer1993-thesis.pdf
get https://csetzer.github.io/articles/ordsyscor010124.pdf                    setzer1999-ordinal-systems.pdf
get https://csetzer.github.io/articles/ordsystwo.pdf                           setzer2000-ordinal-systems-2-inaccessible.pdf
get https://csetzer.github.io/articles/venedig.pdf                             setzer1998-intro-wellordering.pdf
get https://arxiv.org/pdf/2304.00246                                            arai2023-lectures.pdf
get https://epub.ub.uni-muenchen.de/3849/1/16.pdf                              bcw1994-uniform.pdf
get https://epub.ub.uni-muenchen.de/3848/1/3848.pdf                            buchholz1993-kpm-note.pdf
# 文本抽取（可抽取的）；Type 3 位图字体的（mahlo.pdf）要渲染读图
for f in setzer-partI setzer1996-uppermahlo setzer1998-wellordering setzer1993-thesis arai2023-lectures setzer1999-ordinal-systems setzer2000-ordinal-systems-2-inaccessible setzer1998-intro-wellordering; do
  pdftotext -layout "$f.pdf" "$f.txt" 2>/dev/null && echo "text: $f.txt"
done
pdftotext -layout bcw1994-uniform.pdf bcw1994-uniform.ocr.txt 2>/dev/null
pdftotext -layout buchholz1993-kpm-note.pdf buchholz1993-kpm-note.ocr.txt 2>/dev/null
mkdir -p renders
pdftoppm -png -r 150 setzer2000-mahlo.pdf renders/pg          # mahlo.pdf 全部页：用 Read 工具看图
pdftoppm -png -r 170 -f 10 -l 12 bcw1994-uniform.pdf renders/bcw   # BCW §4 与 T(M) 实例（OCR 在数学处不可靠）
pdftoppm -png -r 170 -f 8 -l 11 buchholz1993-kpm-note.pdf renders/bkb   # Buchholz §1 定义与引理
echo done
