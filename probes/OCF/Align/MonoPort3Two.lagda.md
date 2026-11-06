# 一族关系 (二): 第 1 层, 两边动作不同, 经通用核

> 不含记号. 入口 [MonoPort3](MonoPort3.lagda.md). 实例 $\Lambda=2$, 世界 $W$ 固定. [MonoPort2Sound](MonoPort2Sound.lagda.md) 的 `snd` 两边用同一个动作; 这里两边动作 $A_i, A_j$ 不同 (要三条 `HA`: $ii$, $jj$, $ij$), **和的结构的十四种情形都由 [MonoPort3Gen](MonoPort3Gen.lagda.md) 的通用核给出**, 本文件只写:
>
> - 输出关系的律 (`OL`, `pre≼`, `lim≼`): 由 `MonoPort2Rel` 的构造子直接给出;
> - 上下文关系取 $\top$ (第 1 层的上下文只流进动作, 本实例的动作不读它), 路径只有 `self` (树的世界与路径都取单点类型);
> - 节点的一步 `niS₂` (两个动作): 上升走 `MonoPort2Zero.chain₂`, 保留走 `cong0₂` 加归纳.
>
> **定理 `snd₂`**: $x\sqsubseteq x'$ ⇒ 对一切满足三条 `HA` 的动作对, 两个读数都可比. 取 $A_i=A_j$ 就是 `MonoPort2Sound.snd` (`snd₁′`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort3Two {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtFeedTree using (D; hz; hs; hself; ss; accL; outS; ⊲ᴴ↑; n0; n1; _⨾_; nl; ni)
open import OCF.Align.MonoPortBridge using (val)
open import OCF.Align.MonoPort2Rel lW
open import OCF.Align.MonoPort2Zero lW using (ac₀; R₀; HA0; I; rO; rf₁; cong0₂; chain₂)
open import OCF.Align.MonoPort2Sound lW using (ac₁; Ai)
import OCF.Align.MonoPort3Gen as Gen
module G = Gen Λ₂ tt lW k0
```

## §1 输出关系的律

```agda
OL : G.OutLaws
OL = record
  { _≼_ = λ Δ Δ′ → o₁ Δ ⊑ o₁ Δ′
  ; L0 = n0⊑ ; L⨾ = ⨾⊑ ; Lnl = nl⊑ ; Ltr = tr
  ; Lu0ˡ = u0ˡ ; Lu0ʳ = u0ʳ ; Lu1ˡ = u1ˡ ; Lu1ʳ = u1ʳ
  ; Lasˡ = asˡ ; Lasˡ′ = asˡ′ ; Lasʳ = asʳ ; Lasʳ′ = asʳ′ }

o₁pre : ∀ (F : ℕ → P.Df W) k → o₁ (G.preᴰ F k) ≡ preL (λ n → o₁ (F n)) k
o₁pre F zero = refl
o₁pre F (suc k) = cong (λ t → t ⨾ o₁ (F k)) (o₁pre F k)

pre≼ : G.PreLaw OL
pre≼ {a} {a′} {F} {F′} ra ra′ rF rF′ h hF k =
  subst (λ t → (o₁ a ⨾ t) ⊑ (o₁ a′ ⨾ nl (λ n → o₁ (F′ n)))) (sym (o₁pre F k)) (pre⊑ ra ra′ rF rF′ h hF k)

lim≼ : G.LimLaw OL
lim≼ {a} {t} {F} ra rF h = lim⊑ ra rF (λ k → subst (λ u → (o₁ a ⨾ u) ⊑ o₁ t) (o₁pre F k) (h k))
```

## §2 核的实例

```agda
-- 树都在世界 W 里, 路径只有 self
module K = G.Core OL (hs hz) ac₁ k1 ⊤ (λ _ → W) (λ _ → ⊤) (λ _ → C.self) (λ _ _ → ⊤) (λ _ _ → ⊤)
open K using (Act; HA; Sem; Run; Obs; CxLaws; module Steps; cx; inn)

cl : CxLaws
cl = record { cxL = λ _ → cx tt ; cxR = λ _ → cx tt ; cx⨾ = λ _ _ _ _ → cx tt ; cx0ˡ = λ _ _ → cx tt ; cx0ʳ = λ _ _ → cx tt
            ; cxas = λ _ _ _ _ → cx tt ; cxas′ = λ _ _ _ _ → cx tt ; cxpre = λ _ _ _ _ _ → cx tt ; cxlim = λ _ _ _ _ → cx tt }

open Steps cl

-- 三条前提
Sem₂ : D₁ → D₁ → Set
Sem₂ x x′ = ∀ (Aᵢ Aⱼ : Act) → HA Aᵢ Aᵢ → HA Aⱼ Aⱼ → HA Aᵢ Aⱼ → Sem Aᵢ Aⱼ x x′
```

## §3 节点

输出节点的分支, 外层动作作参数 (两边各自的).

```agda
outB : Act → Br → D₁ → P.St W → Br
outB A₀ v ww Z {W′} p lW′ y =
  P.yc (P.BNi ac₁ ac₀ (ss hself) v C.self k1 A₀ ww Z k0 (C.⊲-tr (C.self {W}) p) lW′ (outS (ss (hself {W = W})) y)) (P.tg C.self (⊲ᴴ↑ p k1) lW′)

branch : ∀ (B B′ : Act) (v v′ : Br) ww ww′ → HA0 (Ai B v ww) (Ai B v ww) → HA0 (Ai B′ v′ ww′) (Ai B′ v′ ww′) → HA0 (Ai B v ww) (Ai B′ v′ ww′) →
         (∀ z z′ → val z ≤ val z′ → Sem (P.Ig↾ C.self B) (P.Ig↾ C.self B′) (ap v z) (ap v′ z′)) →
         ∀ (Z Z′ : P.St W) → Good Z → Good Z′ → SRel Z Z′ →
         ∀ z z′ → val z ≤ val z′ → ap (outB B v ww Z) z ⊑ ap (outB B′ v′ ww′ Z′) z′
branch B B′ v v′ ww ww′ hv hv′ hvv cv Z Z′ gZ gZ′ sZ z z′ le =
  proj₂ (cv z z′ le tt tt _ _ azero azero S S′ (cx tt) (G⊕ {Z₁} {Δ} gZ rΔ) (G⊕ {Z₁′} {Δ′} gZ′ rΔ′) (S⊕ {Z₁} {Z₁′} {Δ} {Δ′} gZ gZ′ sZ o) z≤)
  where
  a b : I
  a = P.Ig↾ C.self (Ai B v ww) , hv
  b = P.Ig↾ C.self (Ai B′ v′ ww′) , hv′
  Z₁ = P.cv C.self Z
  Z₁′ = P.cv C.self Z′
  Δ = R₀ (proj₁ a) z C.self n0 Z₁
  Δ′ = R₀ (proj₁ b) z′ C.self n0 Z₁′
  S = Z₁ ⊕ Δ
  S′ = Z₁′ ⊕ Δ′
  o = proj₁ (cong0₂ a b hvv z z′ le) C.self C.self n0 n0 (vY Z) (vY Z′) Z₁ Z₁′ (≤-refl _) gZ gZ′ sZ (proj₁ sZ)
  rΔ = rf₁ (proj₁ (rO a z)) C.self n0 Z₁ gZ
  rΔ′ = rf₁ (proj₁ (rO b z′)) C.self n0 Z₁′ gZ′

module _ (Aᵢ Aⱼ : Act) (hi : HA Aᵢ Aᵢ) (hj : HA Aⱼ Aⱼ) (hij : HA Aᵢ Aⱼ) where
  niS₂ : ∀ {u u′ : Br} → (∀ z z′ → val z ≤ val z′ → Sem₂ (ap u z) (ap u z′)) → (∀ z z′ → val z ≤ val z′ → Sem₂ (ap u′ z) (ap u′ z′)) →
         (∀ z z′ → val z ≤ val z′ → Sem₂ (ap u z) (ap u′ z′)) → Sem Aᵢ Aⱼ (ni (ss hself) u) (ni (ss hself) u′)
  niS₂ {u} {u′} mu mu′ cr tt tt w w′ c c′ Y Y′ _ g g′ s cb =
    chain₂ i j hx Y Y′ c c′ g g′ s cb ,
    ni⊑ (λ z z′ le → branch Aᵢ Aᵢ u u w w h0 h0 h0 (λ z₁ z₁′ l₁ → mu z₁ z₁′ l₁ Aᵢ′ Aᵢ′ hi hi hi) Y Y g g (sr g) z z′ le)
        (λ z z′ le → branch Aⱼ Aⱼ u′ u′ w′ w′ h1 h1 h1 (λ z₁ z₁′ l₁ → mu′ z₁ z₁′ l₁ Aⱼ′ Aⱼ′ hj hj hj) Y′ Y′ g′ g′ (sr g′) z z′ le)
        (λ z z′ le → branch Aᵢ Aⱼ u u′ w w′ h0 h1 hx (λ z₁ z₁′ l₁ → cr z₁ z₁′ l₁ Aᵢ′ Aⱼ′ hi hj hij) Y Y′ g g′ s z z′ le)
    where
    Aᵢ′ = P.Ig↾ C.self Aᵢ
    Aⱼ′ = P.Ig↾ C.self Aⱼ
    h0 : HA0 (Ai Aᵢ u w) (Ai Aᵢ u w)
    h0 z z′ e e′ Z Z′ le gz gz′ sz eb = mu z z′ le Aᵢ′ Aᵢ′ hi hi hi tt tt _ _ e e′ Z Z′ (cx tt) gz gz′ sz eb
    h1 : HA0 (Ai Aⱼ u′ w′) (Ai Aⱼ u′ w′)
    h1 z z′ e e′ Z Z′ le gz gz′ sz eb = mu′ z z′ le Aⱼ′ Aⱼ′ hj hj hj tt tt _ _ e e′ Z Z′ (cx tt) gz gz′ sz eb
    hx : HA0 (Ai Aᵢ u w) (Ai Aⱼ u′ w′)
    hx z z′ e e′ Z Z′ le gz gz′ sz eb = cr z z′ le Aᵢ′ Aⱼ′ hi hj hij tt tt _ _ e e′ Z Z′ (cx tt) gz gz′ sz eb
    i j : I
    i = Ai Aᵢ u w , h0
    j = Ai Aⱼ u′ w′ , h1
```

## §4 定理

```agda
-- 两处 preL 定义相同
preL≡ : ∀ {ly V} (d : ℕ → D ly V) k → G.preL d k ≡ preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)

snd₂ : ∀ {x x′} → x ⊑ x′ → Sem₂ x x′
snd₂ n0⊑ Aᵢ Aⱼ hi hj hij = n0S
snd₂ n1⊑ Aᵢ Aⱼ hi hj hij = n1S hij
snd₂ (⨾⊑ rx rx′ hx hy) Aᵢ Aⱼ hi hj hij =
  ⨾S (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ rx′ Aⱼ Aⱼ hj hj hj) (snd₂ hx Aᵢ Aⱼ hi hj hij) (inn tt) (snd₂ hy Aᵢ Aⱼ hi hj hij)
snd₂ (nl⊑ rd rd′ hd) Aᵢ Aⱼ hi hj hij =
  nlS (λ n → snd₂ (rd n) Aᵢ Aᵢ hi hi hi) (λ n → snd₂ (rd′ n) Aⱼ Aⱼ hj hj hj) (λ n → snd₂ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → inn tt)
snd₂ (ni⊑ mu mu′ cr) Aᵢ Aⱼ hi hj hij =
  niS₂ Aᵢ Aⱼ hi hj hij (λ z z′ le → snd₂ (mu z z′ le)) (λ z z′ le → snd₂ (mu′ z z′ le)) (λ z z′ le → snd₂ (cr z z′ le))
snd₂ (tr h h′) Aᵢ Aⱼ hi hj hij = trS (snd₂ h Aᵢ Aᵢ hi hi hi) (snd₂ h′ Aᵢ Aⱼ hi hj hij)
snd₂ (u0ˡ h) Aᵢ Aⱼ hi hj hij = u0ˡS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (u0ʳ h) Aᵢ Aⱼ hi hj hij = u0ʳS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (u1ˡ h) Aᵢ Aⱼ hi hj hij = u1ˡS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (u1ʳ h) Aᵢ Aⱼ hi hj hij = u1ʳS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (asˡ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asˡS (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ ry Aᵢ Aᵢ hi hi hi) (snd₂ rz Aᵢ Aᵢ hi hi hi) (inn tt) (inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (asˡ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asˡ′S (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ ry Aᵢ Aᵢ hi hi hi) (snd₂ rz Aᵢ Aᵢ hi hi hi) (inn tt) (inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (asʳ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asʳS (snd₂ rx Aⱼ Aⱼ hj hj hj) (snd₂ ry Aⱼ Aⱼ hj hj hj) (snd₂ rz Aⱼ Aⱼ hj hj hj) (inn tt) (inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (asʳ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asʳ′S (snd₂ rx Aⱼ Aⱼ hj hj hj) (snd₂ ry Aⱼ Aⱼ hj hj hj) (snd₂ rz Aⱼ Aⱼ hj hj hj) (inn tt) (inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (pre⊑ {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k) Aᵢ Aⱼ hi hj hij =
  subst (λ t → Sem Aᵢ Aⱼ (x ⨾ t) (x′ ⨾ nl d′)) (preL≡ d k) (preS pre≼ (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ rx′ Aⱼ Aⱼ hj hj hj) (λ n → snd₂ (rd n) Aᵢ Aᵢ hi hi hi) (λ n → snd₂ (rd′ n) Aⱼ Aⱼ hj hj hj)
       (snd₂ hx Aᵢ Aⱼ hi hj hij) (inn tt) (λ n → snd₂ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → inn tt) k)
snd₂ (lim⊑ {x} {t} {d} rx rd h) Aᵢ Aⱼ hi hj hij =
  limS lim≼ (snd₂ rx Aᵢ Aᵢ hi hi hi) (λ n → snd₂ (rd n) Aᵢ Aᵢ hi hi hi) (inn tt) (λ n → inn tt)
       (λ k → subst (λ u → Sem Aᵢ Aⱼ (x ⨾ u) t) (sym (preL≡ d k)) (snd₂ (h k) Aᵢ Aⱼ hi hj hij))
```
