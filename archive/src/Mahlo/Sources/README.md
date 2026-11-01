# 文献缓存

PDF、抽取文本、渲染图**不入库**（见 `.gitignore`），`bash FETCH.sh` 一键重取。逐节的引用边界（每份材料支持什么、不能据此声称什么）在 [../SOURCES.md](../SOURCES.md)。

## 已取得

| 本地文件 | 出处 | 抽取 | 用在哪 |
|---|---|---|---|
| `setzer2000-mahlo.pdf` | Setzer, *Extending ML type theory by one Mahlo-universe*, AML 39 (2000) | **Type 3 位图字体，`pdftotext` 出乱码**；用 `renders/pg-NN.png` 读图 | MLM 规则（Def 4.1/4.3，页 8–11 → [Object/Rules](../Object/Rules.lagda.md)）；`OT` 与 `≺′`（§3，页 5–7）；良序证明 §5（页 14–19）；摘要给 \(|\mathrm{MLM}|=\psi_{\Omega_1}\Omega_{\mathrm M+\omega}\) |
| `setzer-partI.pdf/.txt` | Setzer, *Universes in type theory Part I* | 可抽取 | PER 模型、\(o(\cdot)\) 指派、\((\mathrm{KPM})^+\) 定义、Theorem 5.3/5.4 |
| `setzer1996-uppermahlo.pdf/.txt` | Setzer 1996, Main Lemma | 可抽取 | 转写引理的来源（§104、§107） |
| `setzer1998-wellordering.pdf/.txt` | Setzer, *Well-ordering proofs for ML type theory*, APAL 92 (1998) | 可抽取（55 页） | **路线 B 的蓝本**：一个宇宙的良序证明，\(\psi_{\Omega_1}\Omega_{\mathrm I+\omega}\)；§5 转引其 §3.2–3.5、§4.2–4.4、Lemma 4.17/4.26–4.29/4.31/4.40、Thm 4.41 |
| `setzer1993-thesis.pdf` | Setzer 博士论文 [Se93]（142 页） | 可抽取 | ML_J 的基段规则精确形状（[Object/Rules](../Object/Rules.lagda.md) §4 目前按标准形状录入，**待核对**） |
| `arai2023-lectures.pdf/.txt` | Arai, *Lectures on ordinal analysis*, arXiv:2304.00246 | 可抽取 | \(\mathrm{RM}_i\) 记法、Def 2.2（N=3）、Def 5.3（一般 N）、条件 (9) |
| `bcw1994-uniform.pdf/.ocr.txt` | Buchholz–Cichon–Weiermann, MLQ 40 (1994) | OCR，数学处不可靠，用 `renders/bcw-1[0-2].png` | 范数基本列、Theorem 4、§4 配方、**页 283 的 T(M) 实例** |
| `buchholz1993-kpm-note.pdf/.ocr.txt` | Buchholz, *A note on the ordinal analysis of KPM*, LC'90 | OCR，用 `renders/bkb-*.png` | \(SC\)、Def 1.1/1.2、Lemma 1.2–1.4——`≺` 的原料 |
| `setzer1999-ordinal-systems.pdf` | Setzer, *Ordinal systems*, Sets and Proofs (1999)，2001 更正版 | **Type 3，读图** `renders/ordsys1-*.png` | 「从下面来」的记号系统（只引用更小者）到 BHO；σ-序数系统到 ID_σ |
| `setzer2000-ordinal-systems-2-inaccessible.pdf` | Setzer, *Ordinal systems part 2: One inaccessible*, LC'98 (2000) | **Type 3，读图** `renders/ordsys2-*.png` | I-序数系统，极限强度恰为 KPI；两种良序证明（超限序列法需经典逻辑；distinguished sets 法可在构造理论内做） |
| `setzer1998-intro-wellordering.pdf` | Setzer, *An introduction to well-ordering proofs in MLTT*, 25 Years of CTT (1998) | **Type 3，读图** `renders/venedig-01.png` | **定理**：能定义可达部分的理论，其强度不能被「从下面来」的记号系统表达（§125） |
| `towsner.txt`、`apw-ffgh.txt` | Towsner；Aguilera–Pakhomov–Weiermann | 可抽取 | 早期参考（§56–§57） |

## 未取得

| 文献 | 用途 | 状态 |
|---|---|---|
| Rathjen, *Proof-theoretic analysis of KPM*, AML 30 (1991) | \(\mathcal T(M)\) 与 \(<\) 的定义；核对 BCW 第 7 条的 `Z` 是 \(\psi_{\mathrm M}\) 还是 \(\Omega_\cdot\) | Leeds／Springer 三次连接失败 |
| Dybjer–Setzer, *Induction–recursion and initial algebras*, APAL 124 (2003) | 「外部 Mahlo ≥ KPM」的原话 | ScienceDirect／PhilPapers 403；只有搜索摘要 |
| Dybjer–Setzer, *The extended predicative Mahlo universe*, JLC 34(6) 2024 | 其 Agda 模型的 IIRD 扩展方式 | 只有摘要（"go beyond IIRD"） |

## 读图约定

`renders/pg-NN.png` 是 mahlo.pdf 第 NN 页（150 dpi）。转写时在 SOURCES.md 注明「读图」而非「抽取」。
