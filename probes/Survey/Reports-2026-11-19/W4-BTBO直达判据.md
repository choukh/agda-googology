# W4 的 BTBO 对角线能否直接进入真实塔

后续第二十五批证明了本文共尾条件的逆向。对选定的 Rₘ，共尾返回 K 等价于每个 Rᵢ 整体进入一座塔。首个 R₀ 严格超过 γ₂，而 γ₂ 已有单个实际输入 z 的精确参照表达 F(κz)。当前优先比较旧反馈链第 2 点与真实 W4 高层输出。[第二十五批的定理与路线判断](第二十五批.md)

旧第 2 站已证闭项支配 BTBO 的后继。W4 的 Λ 有合法闭项，已证下界 D 满足 ψ₀(Ω₂) < D < ψ₀(Ω₃)。右侧不等式约束 D，W4 的真实值是否达到 BTBO 仍开放。[旧站定理](../../OCF/Lean/YiPMMinEVEnd.lagda.md) · [W4 的闭下界](第二十四批.md)

## 从 BTBO 倒推

写 sₙ 为 W4 第 n 座独立标准塔折到零层的值，K 为所有 sₙ 的上确界。已有 K ≼ read(Λ)。BTBO 自身是对角列 γ₁、γ₂、… 的上确界。γ₁ 已在 s₁，γ₂ 是 ψ₀(Ω_{ε₀})。仓库分别证明了 ε₀ 层号的读法及 ψ₀(Ω_ω) ≼ γ₂，因此一旦将 γ₂ 搬入真实塔，所有有限 n 的 ψ₀(Ωₙ) 都同时进入。只用这一项仍不足以给出整条 BTBO 对角线。[塔的上确界](../Reports-2026-11-18/attachments/B22TowerCut.agda.txt) · [原对角定义](../../OCF/Align/NoCumsum.lagda.md) · [有限层比较](../Reports-2026-11-18/attachments/B12BtboCut.agda.txt)

第 22 批在第 m+3 座真实塔中选定一个下标 z，并以**参照折叠**读取 z 的层号，得到 Rₘ。z 的位置已在 W4 找到，把 Rₘ 的值搬回 W4 是另一条数学义务。第 22 批的充分条件要求每一个 Rₘ 整体落在某座标准塔。[选取的下标与两种读数](../Reports-2026-11-18/attachments/B22SourceSlots.agda.txt) · [原条件](../Reports-2026-11-18/attachments/B22TowerDiagonal.agda.txt)

## 后继余量与可变塔号

若 γₖ ≼ sₘ₊₁，则 suc(γₖ₊₁) ≼ Rₘ。原下标嵌入能接收最高到 suc(sₘ₊₁) 的源值，因此可送入原层号的后继。原塌缩对层号的这次提升严格增长，给出了输出端所需的后继余量。[严格余量](attachments/QBtboReserve.agda.txt)

于是若再有 Rₘ ≼ K，就有 suc(γₖ₊₁) ≼ K。按后继进入可数极限的值序规则，存在一座标准塔已收下这个后继。下一次可以在更高的塔重新开始。只要对任意起始塔号 i 都有某个 m ≥ i 满足 Rₘ ≼ K，就可以沿 γ 归纳，将整个原 BTBO 放入 K，继而放入真实 Λ。首个具体检验是 R₀ ≼ K。它单独就给出某座真实标准塔同时支配 γ₂ 和所有有限层。若只把 R₀ 放入 Λ，直接传递仍给 γ₂ ≼ read(Λ)，但要沿标准塔接续还需为 γ₂ 找到塔号。这个首例和全称条件均待实填。[首例与统一归纳](attachments/QBtboCofinal.agda.txt)

实填时可以拆开 Rₘ。对任意零层树 a，a ≼ K 当且仅当每个满足 suc(x) ≼ a 的 x，都能找到自己的塔 j 使 suc(x) ≼ sⱼ。正向由后继进入极限抽取塔号，反向对 a 作树归纳。这条定理量化所有相关后继，有限深度测试不能代替它。在 a = K 的实例上，每个后继都有塔接收，而每座 sⱼ 均严格低于 K。对具体 Rₘ，两种条件是否有别仍开放。[充要条件](attachments/QBtboSuccessorCut.agda.txt) · [同一塔与逐后继取塔的区别](attachments/QBtboCutExample.agda.txt)

## 下一步的取舍

若优先取 BTBO，建议直接在 R₀ 的规范分支上找一个随询问选取实际塔的构造，检验同一构造能否随输入塔号升高而复用。另一条已有出口允许把旧第一座正塔的指定对角列逐项送入真实 Λ，每项可取不同的实际位置。它规避了 K 可能覆盖不了某些 Λ 孩子的限制。两者都允许绕开逐站证明，哪项真实搬运先成立尚无定论。[旧对角列的直接出口](../Reports-2026-11-18/attachments/B17Legacy.agda.txt)

## 复核与复现

主审从专题接口为空的目录独立复编两个入口，各自带入一个新模块，四份均有本次 Checking 记录，退出码均为 0。逐字核对第四层的原 BTBO 与真实 W4 闭项两个端点。四份附件与复编源码相同。使用仓库安全选项和 6G 堆。本轮没有使用排中律、选择或函数外延。核对已恢复的第 22 批及之前的 432 份旧实验源码后，复用对应接口。[内部派发与原始回报](BTBO直达-内部回报.md)

复现时，将含标准库和 cubical 的库表路径赋给 shell 变量 `library_file`。从仓库根目录恢复到第 22 批，指定一个入口即可。

```sh
python3 probes/Survey/Reports-2026-11-18/verify.py --batch 22 --library-file "$library_file" B22TowerDiagonal
```

将打印的实验目录记为 `work`，把四份附件恢复到该目录。两个入口分别导入其余两份证明。

```sh
for srcfile in probes/Survey/Reports-2026-11-19/attachments/QBtbo*.agda.txt; do
  name=${srcfile##*/}
  cp "$srcfile" "$work/${name%.txt}"
done
for entry in QBtboCofinal QBtboCutExample; do
  agda +RTS -M6G -RTS --library-file="$library_file" -W noUnsupportedIndexedMatch \
    -i src -i probes -i "$work" "$work/$entry.agda" || exit $?
done
```
