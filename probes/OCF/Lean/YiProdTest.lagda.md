# 产出端的有限测试: 规范计算里卡住的那一对带上证据并保留, 跨支的一对不保留

非验收文件. 有限测试 (`refl`) 与编译定理, 无前提. `T⁺ʷᵖ` (读法 ψ₀(Ω_{Ω+1})) 的消费端吃的是带标注的链 (`T⁺ʷ-form`); 链的第 1 点是根结点 `p₀` (`ch1`), 它在坐标 `ξa` 的分支 (同 [YiDlLost](YiDlLost.lagda.md)) 的第 1 个分量是 `rN` 上的结点 (`gKc-1′`); 这个结点的标注沿 `YiDlLost.occN` 的路径走到 `pN` 上的结点, 证据是 `refl` (`marked`), 有证据时派发保留在 `YiZipLost` 的槽位 (`kept-here`), 消费端在这个结点上保留 (`node-kept`); 不带证据时折叠 (`lost-bare`).
编译定理: 跨支那一对对一切标注只走 `D` (`cross-anyᵖ`), 它的证据类型是空的 (`cross-noEv`); 证据只在进 Ω 结点层号的一支时产生 (`ev-in-branch`), 自派发只传递 (`ev-self`); 内层折叠 (派发的证据处处有) 造的每个结点, 分支里的每个结点都带证据 (`inner-all`, 对一切源树). 不陈述值; 坐标 `ξa` 是不是新折叠在零层被问到没有检查.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiProdTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; R)
open import OCF.Lean.YiLamFold using (Kfk; nrmk; nrmk-lgl; Lw; w0; ws; wl; wΩ; none; at)
open import OCF.Lean.YiDlInst using (V2; ξa; rN)
open import OCF.Lean.YiDlLost using (pN; LN; Vw) renaming (s to sN; a to aN)
open import OCF.Lean.YiZipMove using (mv)
open import OCF.Lean.YiZipWay using (Way′; keep′; fold′; byEq; byMv; _⨾_)
open import OCF.Lean.YiZipFold using (dl′)
open import OCF.Lean.YiCtxFold using (SB)
open import OCF.Lean.YiCtxAnn using (Mk; noM; sucM; limM; lcM; Pv; mE; mS; mL; mB; pB; pL; pM; cmpe₀; cross-anyM)
open import OCF.Lean.YiProdArith
open import OCF.Lean.YiCtxTest using (q₂; r₃)
open import OCF.Lean.YiProdFold
```

## 1 消费端吃带标注的链; 链的第 1 点

```agda
T⁺ʷ-form : T⁺ʷᵖ ≡ G.lim (λ n → Ψᵖ zero V2 (λ r → noS {suc (tw 2)} (inj₂ r)) (λ r → fx zero (suc (tw 2)) (inj₂ r))
  (chT (tw 2) V2 n) noM (chP (tw 2) V2 n))
T⁺ʷ-form = refl

Tt′ : R → Raw (tw 2)
Tt′ η = Φ (tw 2) (Vw (nrmk zero η) (nrmk-lgl zero η)) (subΩ (selfR (tw 2)) (nrmk zero η) (nrmk-lgl zero η)) G.top

gK′ : R → Raw (tw 2)
gK′ ζ = plus (tw 2) G.top (Kfk zero Tt′ ζ)

p₀ : Pre (tw 2)
p₀ = G.top , tt , inj₁ tt

ch1 : chT (tw 2) V2 1 ≡ G.lc p₀ gK′
ch1 = refl

gKc′ : ℕ → Raw (tw 2)
gKc′ n = plus (tw 2) G.top (acc (λ _ z → plus (tw 2) z (Tt′ ξa)) (Kfk zero Tt′ aN) n)

gK-form′ : gK′ ξa ≡ G.lim gKc′
gK-form′ = refl

unws : ∀ {k} → Lw (suc k) → Lw k
unws (ws V) = V

gN′ : Raw LN → Raw (tw 2)
gN′ = Φ (tw 2) (unws (Vw (nrmk zero ξa) (nrmk-lgl zero ξa))) (sub₂ (subΩ (selfR (tw 2)) (nrmk zero ξa) (nrmk-lgl zero ξa)))

Tt-node′ : Tt′ ξa ≡ G.lc rN gN′
Tt-node′ = refl

bN′ : Raw LN → Raw (tw 2)
bN′ η = plus (tw 2) G.top (plus (tw 2) (Kfk zero Tt′ aN) (gN′ η))

gKc-1′ : gKc′ 1 ≡ G.lc rN bN′
gKc-1′ = refl
```

## 2 那个结点的标注

`π₁` 取自链的第 1 点的标注 (坐标 `ξa`, 第 1 个分量). `walk` 沿方向表走到一个结点, 读出它的位置与证据.

```agda
π₁ : Pv (G.lc rN bN′)
π₁ = pL (pB (chP (tw 2) V2 1) ξa) 1

data Dir : Set where
  dS : Dir
  dL : ℕ → Dir
  dT : Dir

walk : ∀ {M} {S : Pre M → Set} → List Dir → (t : Raw M) → Mk S t → Maybe (Σ (Pre M) λ p → Maybe (S p))
walk [] (G.lc r g) μ = just (r , mE μ)
walk (dS ∷ ds) (G.suc a) μ = walk ds a (mS μ)
walk (dL n ∷ ds) (G.lim f) μ = walk ds (f n) (mL μ n)
walk {M} (dT ∷ ds) (G.lc r g) μ = walk ds (g (Lay.tp (Lo M r))) (mB μ _)
walk _ _ _ = nothing

pathN : List Dir
pathN = dL 0 ∷ dL 1 ∷ dL 0 ∷ dL 0 ∷ dL 0 ∷ dT ∷ []

marked : walk pathN (bN′ G.top) (pM π₁ G.top) ≡ just (pN , just refl)
marked = refl

L : LF
L = lev (tw 2) pN

kept-here : cmpe₀ rN pN (just refl) ≡ keep′ sN (byEq refl ⨾ byMv L L)
kept-here = refl

lost-bare : cmpe₀ rN pN nothing ≡ fold′
lost-bare = refl

node-kept : ∀ (g : Raw L → Raw (tw 2)) μ (π : Pv (G.lc pN g)) →
  Ψᵖ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (G.lc pN g) (lcM (just refl) μ) π ≡
    G.lc sN (λ η → Ψᵖ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (g (mv L L η)) (μ (mv L L η)) (pB π (mv L L η)))
node-kept g μ π = refl
```

## 3 证据从哪里来; 跨支那一对

```agda
ev-in-branch : ∀ {k g} (η : Raw k) (l : Lgl k η) r r′ e → evx (subΩ (selfR (lc k g)) η l) r r′ e ≡ just refl
ev-in-branch η l r r′ e = refl

ev-self : ∀ k r r′ e → evx (selfR k) r r′ e ≡ e
ev-self k r r′ e = refl

cross-anyᵖ : ∀ (e : Maybe (SB (tw 2) q₂ r₃)) → cmpe₀ q₂ r₃ e ≡ dl′ (lev (tw 2) q₂) (tw 2) r₃
cross-anyᵖ = cross-anyM

cross-noEv : SB (tw 2) q₂ r₃ → ⊥
cross-noEv ()
```

## 4 内层折叠造的结点: 分支里处处有证据

`AJ t μ`: 标注 `μ` 把 `t` 里 (嵌入以外) 的每个结点都标上证据.

```agda
IsJ : ∀ {A : Set} → Maybe A → Set
IsJ (just _) = ⊤
IsJ nothing = ⊥

AJ : ∀ {M} {S : Pre M → Set} (t : Raw M) → Mk S t → Set
AJ G.zero μ = ⊤
AJ (G.suc a) μ = AJ a (mS μ)
AJ (G.lim f) μ = ∀ n → AJ (f n) (mL μ n)
AJ (G.lc r g) μ = IsJ (mE μ) × (∀ ζ → AJ (g ζ) (mB μ ζ))
AJ (G.em i a) μ = ⊤
AJ G.top μ = ⊤

module _ {j : LF} {h : Raw j → LF} {S : Pre (lc j h) → Set} where
  AJ-plus : ∀ {x} (μx : Mk S x) (a : Raw (lc j h)) μa → NE a → AJ x μx → AJ a μa →
    AJ (plus (lc j h) x a) (plusM μx a μa)
  AJ-plus μx G.zero μa ne ax aa = ax
  AJ-plus μx (G.suc a) μa ne ax aa = AJ-plus μx a (mS μa) ne ax aa
  AJ-plus μx (G.lim f) μa ne ax aa = λ n → AJ-plus μx (f n) (mL μa n) (ne n) ax (aa n)
  AJ-plus μx (G.lc r g) μa ne ax (ja , aa) = ja , λ ζ → AJ-plus μx (g ζ) (mB μa ζ) (ne ζ) ax (aa ζ)
  AJ-plus μx (G.em i a) μa () ax aa
  AJ-plus μx G.top μa ne ax aa = ax

  AJ-acc : ∀ (b : ℕ → Raw (lc j h)) (μb : ∀ n → Mk S (b n)) {x} (μx : Mk S x) → (∀ n → NE (b n)) →
    (∀ n → AJ (b n) (μb n)) → AJ x μx → ∀ n → AJ (acc (λ n z → plus (lc j h) z (b n)) x n) (accM b μb μx n)
  AJ-acc b μb μx nb ab ax zero = ax
  AJ-acc b μb μx nb ab ax (suc n) = AJ-plus _ (b n) (μb n) (nb n) (AJ-acc b μb μx nb ab ax n) (ab n)

  AJ-sac : ∀ {y} (μ : Mk S y) → NE y → AJ y μ → ∀ n → AJ (acc (λ _ z → plus (lc j h) y z) y n) (sacM μ n)
  AJ-sac μ ny ay zero = ay
  AJ-sac {y} μ ny ay (suc n) = AJ-plus μ (acc (λ _ z → plus (lc j h) y z) y n) (sacM μ n) (NE-sac ny n) ay (AJ-sac μ ny ay n)

  AJ-Kfk : ∀ i {T : Raw i → Raw (lc j h)} (μT : ∀ η → Mk S (T η)) → (∀ η → NE (T η)) → (∀ η → AJ (T η) (μT η)) →
    ∀ ξ → AJ (Kfk i T ξ) (KfkM i μT ξ)
  AJ-Kfk i μT nT aT G.zero = aT G.zero
  AJ-Kfk i {T} μT nT aT (G.suc a) =
    AJ-acc (λ _ → T (G.suc a)) (λ _ → μT (G.suc a)) (KfkM i μT a) (λ _ → nT _) (λ _ → aT _) (AJ-Kfk i μT nT aT a)
  AJ-Kfk i μT nT aT (G.lim f) = λ n → AJ-Kfk i μT nT aT (f n)
  AJ-Kfk i μT nT aT (G.lc r g) = AJ-Kfk i μT nT aT (g (Lay.tp (Lo i r)))
  AJ-Kfk zero μT nT aT (G.em () a)
  AJ-Kfk (suc i) μT nT aT (G.em _ a) = AJ-Kfk i _ (λ b → nT _) (λ b → aT _) a
  AJ-Kfk (lim f) μT nT aT (G.em n a) = AJ-Kfk (f n) _ (λ b → nT _) (λ b → aT _) a
  AJ-Kfk (lc k g) μT nT aT (G.em (η , l) a) = AJ-Kfk (g η) _ (λ b → nT _) (λ b → aT _) a
  AJ-Kfk i μT nT aT G.top = aT G.top
```

`σ` 处处给证据时, `Φ` 的输出的每个结点都带证据 (`AJΦ`); 内层折叠的派发的 `evx` 处处给证据, 所以它造的每个结点相对自己的分支处处有证据 (`inner-all`), 例如 `subΩ (selfR _) η l` (`in-branch-ok`).

```agda
AJΦ : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) S σ → (∀ r → IsJ (σ r)) → ∀ t → AJ (Φ _ V x t) (Φmk V x S σ t)
AJΦ V x S σ jσ G.zero = tt
AJΦ V x S σ jσ (G.suc a) = AJ-sac _ (NE-Φ V x a) (AJΦ V x S σ jσ a)
AJΦ V x S σ jσ (G.lim f) = λ n → AJΦ V x S σ jσ (f n)
AJΦ V x S σ jσ (G.lc r g) = jσ r , λ a → AJΦ V x S σ jσ _
AJΦ (ws V) x S σ jσ (G.em _ a) = AJΦ V (sub₂ x) S _ (λ r → jσ _) a
AJΦ (wl V st) x S σ jσ (G.em n a) = AJΦ (V n) (subℕ x n) S _ (λ r → jσ _) a
AJΦ (wΩ V w) x S σ jσ (G.em (η , l) a) = AJΦ (V η l) (subΩ x η l) S _ (λ r → jσ _) a
AJΦ w0 x S σ jσ G.top = AJ-sac noM tt tt
AJΦ (ws V) x S σ jσ G.top = jσ _ , λ a → AJΦ V (sub₂ x) S _ (λ r → jσ _) _
AJΦ (wl V st) x S σ jσ G.top =
  AJ-acc _ _ _ (λ n → NE-Φ (V (suc n)) (subℕ x (suc n)) G.top) (λ n → AJΦ (V (suc n)) (subℕ x (suc n)) S _ (λ r → jσ _) G.top)
    (AJΦ (V 0) (subℕ x 0) S _ (λ r → jσ _) G.top)
AJΦ (wΩ {k} {g} V none) x S σ jσ G.top =
  AJ-acc _ _ _ (λ n → NE-Φ _ (subΩ x _ _) G.top) (λ n → AJΦ _ (subΩ x _ _) S _ (λ r → jσ _) G.top)
    (AJΦ _ (subΩ x _ _) S _ (λ r → jσ _) G.top)
AJΦ (wΩ {k} {g} V (at ρ e)) x S σ jσ G.top =
  jσ _ , λ a → AJ-Kfk k _ (λ η → NE-Φ _ (subΩ x _ _) G.top) (λ η → AJΦ _ (subΩ x _ _) S _ (λ r → jσ _) G.top) _

inner-all : ∀ {j h k} (V : Lw k) (x : PX (lc j h) k) → (∀ r r′ e → IsJ (evx x r r′ e)) → ∀ r t →
  AJ (Φ _ V x t) (Φmk V x (SB _ (pos x r)) (λ r′ → evx x r r′ nothing) t)
inner-all V x hx r t = AJΦ V x _ _ (λ r′ → hx r r′ nothing) t

in-branch-ok : ∀ {k g} (η : Raw k) (l : Lgl k η) r r′ e → IsJ (evx (subΩ (selfR (lc k g)) η l) r r′ e)
in-branch-ok η l r r′ e = tt
```
