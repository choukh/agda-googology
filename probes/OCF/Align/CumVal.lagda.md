# 累加树 `Tψ` 的序数值: 判决 PARTIAL

> **验收文件.** 对象: [CumUpW](CumUpW.lagda.md) 的 `Tψ`. 目标 $\psi_0(\Omega_{\Omega+1})$ 这一站序数值**未证**. 证出的是基线: `Tψ` 自己的 $\psi_0(\Omega_\Omega)$ 这一站 (`TΩ`) 过序数值验收 (`TΩ≈`). 此前定理只对上一轮的 `Tᶜ`, `TΩ` 只有形状测试. 由此 `TΩ+1` 有下界 $\psi_0(\Omega_\Omega)$ (`low-Ω+`). 上界一个也没有. 没有掉值或超值的见证, 也没有证明不掉不超.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.BTBO using (module Trich)
open Trich using (zero; suc)
open FL using (z≅; s≅; l≅; HS) renaming (_≅_ to _≅₀_; ≅-refl⁰ to ≅₀-refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.CumReadCFThm using (Y)
import OCF.Align.CumReadCFThm
open import OCF.Align.CumReadTop using (Tᶜ; ysᶜ; chainᶜ; η)
open import OCF.Align.CumUpW hiding (ord)
open import OCF.Align.CumUpEq using (_≈ᴬ_; z≈; s≈; l≈; ≈ᴬ-refl)
open import OCF.Align.CumUpPsi using (next≈)
open import OCF.Align.CumUpMain using (T-mono)
open import OCF.Align.CumValZ
open import OCF.Align.CumUpAcceptSim using (fr; Y-sim) renaming (Ix to Ixᴸ; iz to izᴸ; is to isᴸ; il to ilᴸ)
open import OCF.Align.CumUpAcceptVal using (Tᶜ≈; Ix-η; τ-SV; z-all; η̂)
open import OCF.Align.BTBOFullLv using (z<SV; ps)
open import OCF.Align.BTBOFullV3 using (Fʸ)
open import OCF.Align.BTBOValDn using (τ)
import OCF.Align.Level as L
import OCF.Align.NoCumsum as N
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼)
```

## §1 `TΩ` 的形状

$\psi_0$ 对闭包节点: 第一支, 然后沿累加下标取分支. 分支的 `oL`, `ow` 透明, 所以每一项就是 `Y` (`val≅`). 世界 `one` 上 `mx` 定义性地取 `one`.

```agda
TΩ TΩ+1 : Ord₀
TΩ   = Tψ 1 azero one g₀ (z⊲ one)
TΩ+1 = Tψ 1 one one g₀ C.self

val₀ : ∀ {k u} (w : Lg k) (e : k ⊲ u) (x : W₀ k u) {c : C.O k} (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : azero ⊲ v) →
       Bz x c → ψ₀ {p = suc zero} {a = azero} (oL zero k e x) gu v gv uv av ≅₀ OCF.Align.CumReadCFThm.ord (C.ψ azero (inj₁ (z⊲ k)) w c)
val₀ w e x gu v gv uv av d with mx gu gv uv (z⊲ v) av
... | mx′ m gm um tm am mv = B₀ (inj₁ (z⊲ _)) w gu m gm um (⊲-tr e um) d

val≅ : ∀ {k u} (w : Lg k) (e : k ⊲ u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : azero ⊲ v) (p : one ⊲ u) →
       ψ₀ {p = suc zero} {a = azero} (oL zero k e (ow p g₀ (Ω̇ zero k))) gu v gv uv av ≅₀ Y k w
val≅ w e gu v gv uv av p = val₀ w e _ gu v gv uv av (bow (B-Ω _))
```

## §2 链

```agda
fr≅₀ : ∀ {a b : Ord₀} → a ≅₀ b → fr a L.≅ fr b
fr≅₀ z≅ = L.z≅
fr≅₀ (s≅ e) = L.s≅ (fr≅₀ e)
fr≅₀ (l≅ h) = L.l≅ (λ n → fr≅₀ (h n))
fr≅₀ (FL.lᵢ≅ {p = ()} e h)
fr≅₀ (FL.upˡ {r = ()} e)
fr≅₀ (FL.upʳ {r = ()} e)

fr⁻ : ∀ (a b : Ord₀) → fr a L.≅ fr b → a ≅₀ b
fr⁻ FL.zero FL.zero e = z≅
fr⁻ (FL.suc a) (FL.suc b) (L.s≅ e) = s≅ (fr⁻ a b e)
fr⁻ (FL.lim f) (FL.lim g) (L.l≅ h) = l≅ (λ n → fr⁻ (f n) (g n) (h n))
fr⁻ FL.zero (FL.suc b) ()
fr⁻ FL.zero (FL.lim g) ()
fr⁻ (FL.suc a) FL.zero ()
fr⁻ (FL.suc a) (FL.lim g) ()
fr⁻ (FL.lim f) FL.zero ()
fr⁻ (FL.lim f) (FL.suc b) ()
fr⁻ (FL.limᵢ () f) b e
fr⁻ (FL.up () x) b e
fr⁻ a (FL.limᵢ () f) e
fr⁻ a (FL.up () x) e

Ix-≈ : ∀ {a b ℓ} → a ≈ᴬ b → Ixᴸ b ℓ → Ixᴸ a ℓ
Ix-≈ z≈ izᴸ = izᴸ
Ix-≈ (s≈ e) (isᴸ d) = isᴸ (Ix-≈ e d)
Ix-≈ (l≈ h) (ilᴸ d) = ilᴸ (λ n → Ix-≈ (h n) (d n))

module Ch where
  gm = g₀
  um : one ⊲ one
  um = C.self

  val : Ix one → Ord₀
  val i = ψ₀ {p = suc zero} {a = azero} (oL zero (Ix.η i) C.self (ow (pos (Ix.gη i)) g₀ (Ω̇ zero (Ix.η i)))) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (z⊲ (Ix.η i))

  y₀ : Ord₀
  y₀ = ψ₀ {p = suc zero} {a = azero} (oL zero one C.self (Ω̇ zero one)) g₀ one g₀ C.self (z⊲ one)

  y₀≅ : y₀ ≅₀ ysᶜ 0
  y₀≅ = val₀ tt C.self (Ω̇ zero one) g₀ one g₀ C.self (z⊲ one) (B-Ω one)

  ch≈ : ∀ n → Ix.η (ixs g₀ y₀ val n) ≈ᴬ η (chainᶜ n)
  val≅′ : ∀ n → val (ixs g₀ y₀ val n) ≅₀ ysᶜ (suc n)

  ch≈ zero    = next≈ (≈ᴬ-refl one) y₀≅
  ch≈ (suc n) = next≈ (ch≈ n) (val≅′ n)

  val≅′ n = fr⁻ _ _ (L.≅-trans (fr≅₀ (val≅ (lgw (Ix.gη i)) C.self (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (z⊲ (Ix.η i)) (pos (Ix.gη i))))
                     (L.≅-trans (Y-sim (lgw (Ix.gη i)) (Ix-≈ (ch≈ n) (Ix-η n)) (z<SV (τ-SV (η̂ (suc n))) ps))
                                (L.≅-sym (z-all (suc n)))))
    where i = ixs g₀ y₀ val n

  ys≅ : ∀ n → yss g₀ y₀ val n ≅₀ ysᶜ n
  ys≅ zero    = y₀≅
  ys≅ (suc n) = val≅′ n
```

## §3 定理

```agda
TΩ≅Tᶜ : TΩ ≅₀ Tᶜ
TΩ≅Tᶜ = l≅ Ch.ys≅

TΩ≈ : fr TΩ ≈ᵛ N.BTBOᴵ
TΩ≈ = ≼-trans (≅→≼ (fr≅₀ TΩ≅Tᶜ)) (proj₁ Tᶜ≈) , ≼-trans (proj₂ Tᶜ≈) (≅→≼ (L.≅-sym (fr≅₀ TΩ≅Tᶜ)))
```

## §4 单侧: 下界

`T-mono` 与 `TP-step` 给 $\sqsubseteq^0$, 所以 $\psi_0(\Omega_\Omega)$ 是整族 $(p+1,a)$ 的下界. **上界: 没有任何一站.** 这只是单调性加基线, 不说明 $\psi_0(\Omega_{\Omega+1})$ 的值.

```agda
open FL using (≺z; ≺s; ≺l; _≺_; _⊑⁰_) renaming (≺i to ≺i₀; ≺u to ≺u₀)
open import OCF.Align.CumUp using (TP; TP-step)

≺→s≼ₑ : ∀ {c b : Ord₀} → c ≺ b → fr (FL.suc c) ≼ fr b
≺→s≼ₑ (≺z e) = s≼s (≅→≼ (fr≅₀ e))
≺→s≼ₑ (≺s h) = ≼-suc (≺→s≼ₑ h)
≺→s≼ₑ (≺l n h) = ≼l n (≺→s≼ₑ h)
≺→s≼ₑ (≺i₀ {p = ()} x ex h)
≺→s≼ₑ (≺u₀ {r = ()} h)

⊑→≼₀ : ∀ (a : Ord₀) {b : Ord₀} → a ⊑⁰ b → fr a ≼ fr b
⊑→≼₀ FL.zero k = z≼
⊑→≼₀ (FL.suc a) k = ≺→s≼ₑ (k (≺z (≅₀-refl a)))
⊑→≼₀ (FL.lim f) k = l≼ (λ n → ⊑→≼₀ (f n) (λ h → k (≺l n h)))
⊑→≼₀ (FL.limᵢ () f) k
⊑→≼₀ (FL.up () x) k

TP≥ : ∀ p → fr (TP 1) ≼ fr (TP (suc p))
TP≥ zero    = ≼-refl _
TP≥ (suc p) = ≼-trans (TP≥ p) (⊑→≼₀ (TP (suc p)) (TP-step (suc p)))

low-Ω+ : ∀ p a u₁ (g : Gw u₁) (e : a ⊲ u₁) → N.BTBOᴵ ≼ fr (Tψ (suc p) a u₁ g e)
low-Ω+ p a u₁ g e =
  ≼-trans (proj₂ TΩ≈) (≼-trans (TP≥ p) (⊑→≼₀ (TP (suc p)) (T-mono (suc p) g₀ g (z⊲ one) e (z⊲ a))))

low-Ω+1 : N.BTBOᴵ ≼ fr TΩ+1
low-Ω+1 = low-Ω+ 0 one one g₀ C.self
```

## §5 为什么 `Ψ-emb`, `V1..V3` 不够 (判断, 未编译)

`Sm` 与本文的 `Bz` 只覆盖没有闭包的层: 分支是 $\Omega_v$ 本身, 所以 `Ψ-emb` 直接比较 $\psi^0(\Omega_a)$. $\Omega+1$ 起分支在上下文里. $\psi_0(\Omega_{\Omega+1})$ 的第 1 项是 $\psi_0(\psi_\Omega(\Omega_\Omega))$, 闭包节点穿过高目标还是闭包 (`ψ⁰ q t (oc x h) = oc …`), 下一步要比较的是 $\psi_0(B(\eta))$ 对 $\psi_0(B(\hat\eta))$, $B$ 是任意上下文. 缺三件:

1. **带基底的嵌入.** 上下文里已有下标低于世界的节点 (`od`, `k ≪ u`), 它们在两边是同一个下标, 所以 $E$ 必须在基底上是恒等. `PEmb` 和 `V1..V3` 不保这一点.
2. **对照树一侧的单调.** 过基本列验收的树 (`Good-θ`, `OCF.Free`) 走 `O`, `Run`, `Ordˢ`, `forceᴺ`, 地板和 `tl` 都在折叠路径上. `Le` 只写在 `Ordᶜ` 上, 那边没有对应物.
3. **两边的值严格性.** `V1`, `V2` 要 `St`. `St-x`, `St-γ` 只对 `S.Ord`, `Ordᶜ`. `𝓞` 的 `WF` 和 `Goodᴺ` 都只给 `HS`, 不给严格.

行数估计 (判断): 这三件合计超过 3000 行. 这些只是未走通的理由, 不是否定.

## §6 试过, 没有结果

把 `TΩ+1` 的字面路径 `≼l 1 (≼l 0 (≼l 0 (≼l 2 (≼l 0 (≼l 0 (≼l 2 _))))))` 代入临时文件想读 $\psi_0(\Omega_\Omega)+1\preccurlyeq$ `TΩ+1` 的严格下界, 12G 堆耗尽 (退出前 `agda: Heap exhausted`). 所以 `TΩ+1` 严格高于 `TΩ` 这件事**未证**, 只有手算的路径和 `ctl-TF` 的形状差. 这不是否定.
