# 和形式, 高度取 $A$: 验收

> **验收文件.** 读 `Value` (序数值的序 `_≼_`) 与 `TLRuleVar` (树到 `Ordᶜ` 的 `trA`, `≤→≼`). 入口 [SumHt](SumHt.lagda.md).
>
> 这里只有一件事: 把 [SumHtGrow](SumHtGrow.lagda.md) 的严格增长 (`_≤_`, 布劳威尔树上) 搬到验收用的序 `_≼_` 上. **没有与带标签的树的比较**: 各站与 $\psi_0(\Omega_{\Omega+2})$, $\psi_0(\Omega_{\Omega\cdot2})$, $\psi_0(\Omega_{\Omega\cdot\omega})$, $\psi_0(\Omega_{\Omega^2})$ 的对照树之间既没有上界也没有下界, 连 `T 1 0` 与 `BTBOᴵ` 也没有 (`SumOne` 的 `T₀≈` 是对另一个折叠证的). 读法是判断.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumHtAccept where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Align.CumReadCF using (asuc)
open import OCF.Align.Value using (_≼_)
open import OCF.Align.TLRuleVar using (trA; ≤→≼)
open import OCF.Align.SumHtClosed using (T; Tω; T²; TΩ+1; TΩ+2; TΩ·2; TΩ·ω; TΩ²)
open import OCF.Align.SumHtGrow using (S1; S2; S3; S4; Ω+1<Ω+2; Ω+2<Ω·2; Ω·2<Ω·ω; Ω·ω<Ω²; lt-up; lt-ω)
```

```agda
v-Ω+1<Ω+2 : trA (asuc TΩ+1) ≼ trA TΩ+2
v-Ω+1<Ω+2 = ≤→≼ Ω+1<Ω+2

v-Ω+2<Ω·2 : trA (asuc TΩ+2) ≼ trA TΩ·2
v-Ω+2<Ω·2 = ≤→≼ Ω+2<Ω·2

v-Ω·2<Ω·ω : trA (asuc TΩ·2) ≼ trA TΩ·ω
v-Ω·2<Ω·ω = ≤→≼ Ω·2<Ω·ω

v-Ω·ω<Ω² : trA (asuc TΩ·ω) ≼ trA TΩ²
v-Ω·ω<Ω² = ≤→≼ Ω·ω<Ω²

v-S1 : ∀ n a → trA (asuc (T n a)) ≼ trA (T n (suc a))
v-S1 n a = ≤→≼ (S1 n a)

v-up : ∀ n a → trA (asuc (T n a)) ≼ trA (T (suc n) 0)
v-up n a = ≤→≼ (lt-up n a)

v-ω : ∀ n a → trA (asuc (T n a)) ≼ trA Tω
v-ω n a = ≤→≼ (lt-ω n a)
```
