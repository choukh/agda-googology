# 跨高度单调: $\psi_0(\Omega_{\Omega\cdot\omega})$ 的记号无关证书

> **判决: HOLDS (编译过的定理, 无条件, `--safe`).**
>
> `Tω-mono : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → forceᴺ _ (GᴺTωn n ev z) ⊑ forceᴺ _ (GᴺTωn (suc n) ev z)`
>
> `GᴺTω : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tω ev z))`
>
> 闭项 `Tω₀ : Ordᶜ zero`, `HSᵀ`, `levelᵀ`, `fgh = FGH Tω₀` ([LadderMonoClosed](LadderMonoClosed.lagda.md)), 没有任何参数. 标签 ([LadderMonoAccept](LadderMonoAccept.lagda.md), 克隆世界): `Tω-cert-label : Lab (forceᴺ _ (GᴺTω ev p)) tω`, `tω` 是 $\psi_0(\Omega_{\psi_1(1)})$.
>
> **比预想的便宜: 不需要跨塔模拟.** 上一轮的判断 ([LadderNF](LadderNF.lagda.md)) 以为要比较 $\bar\psi_n(x)$ 与 $\bar\psi_{n+1}(\iota_\downarrow x)$ 对一切 $x$, 于是要 `top` 对 `pD top`, `pψ r C` 对 `pD (pΨ zero … C′)`, 还要记 `omk` 的不变量 $x=\iota\,r\,z$. 这是多余的. 只比较 $T_n$ 与 $T_{n+1}$ 的**基本列最前面的那一项**:
>
> 1. $T_{m+2}$ 是闭包 (`qcl`), `Goodᴺ` 要它的第一个点好: $\bar\psi_{m+1}(\iota_\downarrow(\dot\Omega_m\,1))$ (`fst-pt`).
> 2. $\dot\Omega_m\,1$ 是 `qΩ` 节点, 所以这个点是链的极限, 第 0 项的链点是 $\dot\Omega_m\,0$, `ι↓` 经 `omk` 的第二格读到它: 第 0 项是 $\bar\psi_{m+1}(\iota_\downarrow(\dot\Omega_m\,0))$ (`lim-term`).
> 3. $\dot\Omega_m\,0$ **没有高度 $m$ 的节点**, 也没有顶层的 `omk`: 它的 `qΩ` 全被里面一层 `ι↓` 变成了高度 $<m$ 的 `qΩ↓`. 所以 $\bar\psi_m$ 与 $\bar\psi_{m+1}$ 在它上面走完全相同的路 (`Dn`, `D-Ψ`, `D→≈ᵠ`, `D-self`), 值 $\cong T_{m+1}$.
>
> 于是 $T_{m+1}\cong T_{m+2}[\text{第一点}][0]\sqsubseteq T_{m+2}$. $T_0\sqsubseteq T_1$ 同形, 在根层走 `limᵢA` (`lim-i`, `mono-0`). 证明对任意两张证书成立 (`mono-s`, `mono-0` 的 `A`, `B`), 不展开 `GᴺTᵠ`.
>
> **`Dn` 的形状.** 两边的节点全在高度 $<m$, `q` 对 `suc q`, 不含 `qΩ` 和 `omk` 两个构造子. 结论是普通的 `Rq` (`D-Ψ`), 因为 `Ψ` 的输出在同一个 `Q H t` 里. `D-ι↓`: 对任何 `Rq n k k′ x x′`, `ι↓ x` 与 `ι↓ (ι↓ x′)` 有 `Dn`; `ι↓` 把 `omk r z x` 变成 `ι↓ z`, 两边都读 $z$, 所以用不到 $x=\iota\,r\,z$.
>
> **不按阶段定制.** `D-Ψ`, `chD`, `D→≈ᵠ`, `D-ι↓` 是对证据的结构递归, 没有对 $m$ 的归纳, 也没有支配论证 (本篇根本不比较大小, 只取已有证书的一项). `D-self` 的两行与 `mono-0`/`mono-s` 的两行来自 `Ω̇` 与 `Tωn` 定义本身的两行.
>
> **否定结果: 无新增.** 只有 `no-top`, 那是下面评估用的小事实.
>
> **受记号影响的形状 (如实说).** 本篇没有新的文法, 树全部来自 `LadderNFTree`, 那张账在 [LadderNF](LadderNF.lagda.md) 里. 特别地, `Tωn zero` 是 $\psi_0(1)$, 第 $n+1$ 项是 $T^\varphi_n$, 这个基本列是记号的 $\Omega\cdot\omega$ 的基本列. 所以这是"证书记号无关", 不是"树自足". 本篇证明的设计只读树; 但"前提为真"是预先由 `Tω-mono-lab` (读记号) 知道的.
>
> **审计 (本文件以外跑).**
>
> - 导入闭包: `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono OCF.Align.LadderMonoClosed`: 禁用表命中 0, `--only` 之外 0; 闭包内没有 `LadderNFW*`, `LadderNFAccept`, `ScafLadder*`, `LadderMonoW*`, `LadderMonoAccept`. `LadderMonoMain` 同样.
> - 定义级切片 `depslice.py`: `GᴺTω` 974 块, 记号 0, 词命中 0; `Tω-mono` 971 块, 0, 0; `Tω₀` 978 块, 0, 0; `fgh` 980 块, 0, 0. 正对照 `Tω-cert-label`: 2450 块, 记号 92, 词命中 378.
> - 切片是语法级的; 闭包是编译器保证的, 但不说明定义没有受记号启发.
>
> **没有做到的.** (1) 标签贴在克隆世界的证书上, 跨世界的联系是代码逐字相同和有限测试, 与 `LadderNFAccept` 的边界相同. (2) FGH 只有有限测试: `fgh 0 = 1`, `fgh 1 = 2`, 与几个形状 ([LadderMonoClosed](LadderMonoClosed.lagda.md) §2); `fgh 2` 的 `refl` 在 170 秒内没有结果, 不是否定.
>
> **下一步的评估: $\psi_0(\Omega_{\Omega\cdot\omega+1})=\psi_0(\Omega_{\psi_1(1)+1})$ (判断, 没有写树, 没有试).** 编译过的只有 [LadderMonoNext](LadderMonoNext.lagda.md) 的 `no-top`, `Ω↓⊑`, `Ω↓↓⊑`.
>
> - **现有的 `Q m` 不够** (`no-top`): 输入要含一切高度的节点, 不在任何 `Q m α` 里; $\Omega\cdot(m+1)+\alpha$ 对可数 $\alpha$ 也够不到 $\Omega\cdot\omega+1$.
> - **ℕ 作高度**标签**到 $\psi_1(1)+\Omega$ 之前够用.** $\Omega\cdot\omega+\alpha$ 的 `qΩ` 是字面的顶层, 不需要标签; 下面的高度仍是 ℕ, `Fv`, `upd`, `tri` 不用改. 要改的是界: `Q₊` 的 $m$ 换成 $\mathbb N\cup\{\infty\}$, $n<^L\infty$ 恒真, `lo ∞ ζ = ζ`. $\psi_1(1)+\Omega$ 起 $\infty$ 本身要当节点的高度, 才真的超出 ℕ (与 `noTimes` 的旧判断一致).
> - **新的行是 $\dot\Omega_\infty\,0$:** `ql F`, $F\,0=1$, $F(n+1)=\iota_{\downarrow\infty}(\dot\Omega_n\,0)$. 规则 `gl` 要**上下文里的**单调 `F n ⊑ᵗ F (suc n)`, 比本篇的单调强. 它在有限高度的影子已经编译过 (`Ω↓⊑`, `Ω↓↓⊑`), 由现成的 `cl-rᵀ`, `Ωz↓`, `ιD-cong` 给; $\infty$ 处还差 $\iota_{\downarrow\infty}(\iota_\downarrow x)$ 与 $\iota_{\downarrow\infty}x$ 的 `Rq`, 形状与 `D-ι↓` 相同.
> - **预期的第一个障碍 (没试):** `Ω̇G` 的 $\infty$ 行要给 `ql F` 的 `VisQ`; 以及标签一侧 `tω` 不在 `NF₁` (`Sb` 不含 $\psi_1(1)$, 见 `ScafLadderQTop`), 验收要先扩这个. 把闭包定理对界参数化是工程量: `LadderNF{Good,Vis,Read,Iota,Tr,Add,Psi,PsiH,Eval,Tail,Mono,Root,Omega,Class,ClassF}` 这 15 个模块里含 `<ᴸ` 的行只有 10 行 (grep 计数, 不是证明; `Tree`, `Rel`, `Cx`, `Rules*` 另算).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 没有模块参数形式的假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMono where

open import OCF.Align.LadderMonoMain public using (Tω-mono; GᴺTω; mono-s; mono-0)
open import OCF.Align.LadderMonoDown public using (D-ι↓; D-self)
open import OCF.Align.LadderMonoRel public using (Dn; D-Ψ; D→≈ᵠ)
open import OCF.Align.LadderMonoClosed public using (Tω₀; HSᵀ; levelᵀ; fgh; Tω₀-indep; fgh-indep)
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [LadderMonoRel](LadderMonoRel.lagda.md) | 关系 `Dn`, `D-Ψ`, `chD`, `D→≈ᵠ` |
| [LadderMonoDown](LadderMonoDown.lagda.md) | `D-ι↓`, `D-tl`, `D-tlΩ`, `D-self` |
| [LadderMonoMain](LadderMonoMain.lagda.md) | `fst-pt`, `lim-term`, `lim-i`, `mono-s`, `mono-0`, `Tω-mono`, `GᴺTω` |
| [LadderMonoClosed](LadderMonoClosed.lagda.md) | 闭项 `Tω₀`, `fgh`, 环境无关, 有限测试 |
| [LadderMonoAccept](LadderMonoAccept.lagda.md) | 验收, 标签 `Tω-cert-label` (不在闭包内) |
| [LadderMonoNext](LadderMonoNext.lagda.md) | 下一步的小事实 `no-top`, `Ω↓⊑`, `Ω↓↓⊑` |
| `LadderMonoW{Rel,Down,Main}` | 机械克隆, 落在标签阶梯的树上, 只供验收 |
