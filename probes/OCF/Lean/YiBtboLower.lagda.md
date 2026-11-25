# BTBO 是下一站闭项的下界 (无前提)

验收文件. 编译定理 `btbo⁺ : D.BTBOᴵ ≼ NA.read NT.T⁺` 与 `src-btbo⁺` (已发表的 BTBO, 经 `BTBO≈`), 不用 `FUNC`, `KEYsuc`, `SpineT`, `ChainP`, 也不用值单调的假设. 链上的不变量只是值序 `D.γ n ≼ read (co (pts m))`; 每一步把值序换成累加规范化层号上的嵌入 (`V2′`), 再嵌进主线折叠值的字面前驱 (`V3m`, 对一切合法层号; 极限情形用主线顶上的部分和与 `Blk` 逐块对上), 最后平移到下一个链点 (`shift-κ`). 不否定也不涉及上界. 第七次独立审查的试验 (2026-11-11), 主审移入并冷编复核.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBtboLower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanLegal using (dnLc; add-cp; Ψ-cp; Ψn-dn; ΨN-dn)
open import OCF.Lean.YiLeanTw3 using (R; ⌜_⌝; lv; F; F-lgl; T₃; pts; obs; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read; read-plus; plus≽)
open import OCF.Lean.YiLeanValFin using (cp⊑; κ; HS-read; lower-read)
open import OCF.Lean.YiFlatChain using (Z-top; lead0)
open import OCF.Lean.YiPEStep using (Fκ; shift-κ)
open import OCF.Lean.YiPEBase using (EmbTⁿ; btbo-embⁿ; btbo-emb⁺)
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono)
open S using (ordᴰ)
import OCF.Align.Level as L
open L using (Ordᶜ)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; _≈ᵛ_)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValNeg using (add-≺)
open import OCF.Align.BTBOFullQ using (<ᴰ-irrefl; clash-lt)
open import OCF.Align.BTBOFullEb using (module Blocks; Inv; inl; inr; inv)
open import OCF.Align.BTBOFullV3 using (𝕋₀; bkᴵ; ≺→⊑₀; add-left)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullLv using (SV-L)
open import OCF.Align.BTBOFull using (St-bk; bk≅γ; BTBO≈)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-∘)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.NoCumsum as N
open import OCF.Lean.YiBtboV2 using (Mono; mz; ms; ml; V2′)

module WT = Blocks 𝕋₀

T₀ : Set
T₀ = Ordᶜ L.zero

-- §0 两个参照是同一个 (定义性)
_ : D.γ ≡ N.γ
_ = refl

_ : D.L ≡ N.L
_ = refl

_ : D.BTBOᴵ ≡ N.BTBOᴵ
_ = refl

-- §1 第 0 层的树抄成 src 的第 0 层树
cp : R → S.Ord₀
cp G.zero = S.zero
cp (G.suc a) = S.suc (cp a)
cp (G.lim f) = S.lim (λ n → cp (f n))
cp (G.lc () g)
cp (G.em () a)
cp G.top = S.suc S.zero

cp≅ : ∀ η → tr₀ (cp η) L.≅ read η
cp≅ G.zero = L.z≅
cp≅ (G.suc a) = L.s≅ (cp≅ a)
cp≅ (G.lim f) = L.l≅ (λ n → cp≅ (f n))
cp≅ (G.lc () g)
cp≅ (G.em () a)
cp≅ G.top = L.s≅ L.z≅

Mono-cp : ∀ η → Lgl zero η → Mono (tr₀ (cp η))
Mono-cp G.zero l = mz
Mono-cp (G.suc a) l = ms (Mono-cp a l)
Mono-cp (G.lim f) (st , lf) = ml (λ n → Mono-cp (f n) (lf n))
  (λ n → ≼-trans (≅→≼ (cp≅ (f n)))
    (≼-trans (⊑→≼ (read (f n)) (cp⊑ (f n) (f (suc n)) (st n))) (≅→≼ (L.≅-sym (cp≅ (f (suc n)))))))
Mono-cp (G.lc () g) l
Mono-cp (G.em () a) l
Mono-cp G.top l = ms mz

-- §2 主线折叠的两条第一位置事实
topfp : ∀ m {k} (V : Lv k) (x : Ext m k) → Cp m G.top (Ψ m V x G.top)
topfp m v0 x = inj₂ (0 , inj₁ refl)
topfp m (vs {k} V) x = inj₂ (Ψn-dn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
  (topfp m V (λ r → x (inj₂ r))))
topfp m (vl V st) x = inj₂ (0 , topfp m (V 0) (λ r → x (0 , r)))

PB : ∀ {M k} → Lv M → Bld M k → Set
PB {M} {k} V′ B = ∀ r g {z} → Cp zero z (Ψ zero V′ (λ _ → fold) (g (Lay.tp (Lo k r)))) →
  Dn zero z (Ψ zero V′ (λ _ → fold) (B r g))

pbLc : ∀ {M} (V′ : Lv M) → PB V′ G.lc
pbLc {M} V′ r g h = ΨN-dn zero M r fold _ _ h

succfp : ∀ {M} (V′ : Lv M) k (B : Bld M k) → PB V′ B → ∀ X →
  Cp zero (succ zero (Ψ zero V′ (λ _ → fold) X)) (Ψ zero V′ (λ _ → fold) (add k B X G.top))
succfp V′ zero B pb X = inj₁ refl
succfp V′ (suc k) B pb X =
  inj₂ (pb (inj₁ tt) _ (succfp V′ k (λ r → B (inj₂ r)) (λ r → pb (inj₂ r)) X))
succfp V′ (lim f) B pb X = inj₂ (0 , succfp V′ (f 0) (λ r → B (0 , r)) (λ r → pb (0 , r)) X)
succfp V′ (lc j g) B pb X = inj₁ refl

-- 后继层号上的折叠值严格高于前一层号上的.
Fsuc : ∀ a (l : Lgl zero a) → read (F a l) L.≺ read (F (G.suc a) l)
Fsuc a l = L.≺l 1 (s₂ (s₁ A≺))
  where
  k = ⌜ a ⌝
  V = lv a l
  y = Ψ zero V (λ _ → fold) G.top
  A≺ : read y L.≺ read (succ zero y)
  A≺ = L.≺l 1 (L.≺-respʳ (lead0 (read y) (Z-top V (λ _ → fold))) (L.≅-sym (read-plus y y)))
  s₁ : read (succ zero y) L.⊑ read (Ψ zero V (λ _ → fold) (plus k G.top G.top))
  s₁ = cp⊑ _ _ (succfp V k G.lc (pbLc V) G.top)
  s₂ : read (Ψ zero V (λ _ → fold) (plus k G.top G.top)) L.⊑
       read (Ψ zero V (λ _ → fold) (plus k G.top (Ψ k V (self k) G.top)))
  s₂ = cp⊑ _ _ (Ψ-cp zero V (λ _ → fold) (add-cp k G.lc dnLc G.top (topfp k V (self k))))

-- §3 V3m: 累加规范化的层号嵌进主线折叠值的字面前驱 (主线一侧的 V3)
lift≺ : ∀ {a b : T₀} → a L.≺ b → ∀ {x : T₀} → x L.≺ L.suc a → x L.≺ b
lift≺ ab (L.≺z e) = L.≺-respˡ (L.≅-sym e) ab
lift≺ ab (L.≺s h) = ≺→⊑₀ ab h

V3m : ∀ η (l : Lgl zero η) →
  Σ (WT.Eb (ordᴰ (cp η)) (read (F η l))) (λ e → ∀ {c} (p : c B.< ordᴰ (cp η)) → L.𝟎 {L.zero} L.≺ WT.map e p)
V3m G.zero l = WT.Eb-zero , λ ()
V3m (G.suc a) l = WT.Eb-suc (proj₁ (V3m a l)) (read (F a l)) (λ h → h) (Fsuc a l) , nzS
  where
  nzS : ∀ {c} (p : c B.< B.suc (ordᴰ (cp a))) →
    L.𝟎 {L.zero} L.≺ WT.map (WT.Eb-suc (proj₁ (V3m a l)) (read (F a l)) (λ h → h) (Fsuc a l)) p
  nzS B.zero = Z-top (lv a l) (λ _ → fold)
  nzS (B.suc p) = proj₂ (V3m a l) p
V3m G.top l = WT.Eb-suc {Bd = L.𝟎} WT.Eb-zero (L.suc L.zero) (λ ()) topLt , nzT
  where
  topLt : L.suc L.zero L.≺ read (F G.top l)
  topLt = L.≺l 0 (L.≺l 1 (L.≺z (L.s≅ L.z≅)))
  nzT : ∀ {c} (p : c B.< B.suc B.zero) →
    L.𝟎 {L.zero} L.≺ WT.map (WT.Eb-suc {Bd = L.𝟎} WT.Eb-zero (L.suc L.zero) (λ ()) topLt) p
  nzT B.zero = L.≺z L.z≅
  nzT (B.suc ())
V3m (G.lc () g) l
V3m (G.em () a) l
V3m (G.lim f) (st , lf) = BL.Lim , nzL
  where
  O : ℕ → Ordᴰ
  O n = ordᴰ (cp (f n))
  Fs : ℕ → R
  Fs n = F (f n) (lf n)
  P : ℕ → T₀
  P n = read (psum zero Fs n)
  P+ : ∀ n → (P n L.+ read (Fs (suc n))) L.≅ P (suc n)
  P+ n = L.≅-sym (read-plus (psum zero Fs n) (Fs (suc n)))
  P≺ : ∀ n → P n L.≺ P (suc n)
  P≺ n = L.≺-respʳ (lead0 (P n) (Z-top (lv (f (suc n)) (lf (suc n))) (λ _ → fold))) (P+ n)
  Pnz : ∀ n → L.𝟎 {L.zero} L.≺ P n
  Pnz zero = Z-top (lv (f 0) (lf 0)) (λ _ → fold)
  Pnz (suc n) = ≺→⊑₀ (P≺ n) (Pnz n)
  Bd : ℕ → T₀
  Bd zero = P 0
  Bd (suc n) = L.suc (P (suc n))
  e₀ : WT.Eb (O 0) (Bd 0)
  e₀ = proj₁ (V3m (f 0) (lf 0))
  eN : ∀ n → WT.Eb (O (suc n)) (read (Fs (suc n)))
  eN n = proj₁ (V3m (f (suc n)) (lf (suc n)))
  N′ : ∀ n {d} → d B.< B.suc (O (suc n)) → T₀
  N′ n B.zero = P (suc n)
  N′ n (B.suc p) = P n L.+ WT.map (eN n) p
  in≺ : ∀ n {d} (p : d B.< O (suc n)) → (P n L.+ WT.map (eN n) p) L.≺ P (suc n)
  in≺ n p = L.≺-respʳ (add-≺ (P n) (WT.below (eN n) p)) (P+ n)
  Nb : ∀ n {d} (p : d B.< B.suc (O (suc n))) → N′ n p L.≺ Bd (suc n)
  Nb n B.zero = L.≺z (L.≅-refl⁰ (P (suc n)))
  Nb n (B.suc p) = L.≺s (in≺ n p)
  Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O (suc n))) (q : d₂ B.< B.suc (O (suc n))) → d₁ B.< d₂ → N′ n p L.≺ N′ n q
  Nm n B.zero    B.zero    r = ⊥-elim (<ᴰ-irrefl r)
  Nm n B.zero    (B.suc q) r = ⊥-elim (clash-lt r q)
  Nm n (B.suc p) B.zero    r = in≺ n p
  Nm n (B.suc p) (B.suc q) r = add-≺ (P n) (WT.mono (eN n) p q r)
  Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O (suc n))) (q : d₂ B.< B.suc (O (suc n))) → d₁ ≡ d₂ → N′ n p L.≅ N′ n q
  Nc n B.zero    B.zero    r = L.≅-refl⁰ _
  Nc n B.zero    (B.suc q) refl = ⊥-elim (<ᴰ-irrefl q)
  Nc n (B.suc p) B.zero    refl = ⊥-elim (<ᴰ-irrefl p)
  Nc n (B.suc p) (B.suc q) r = L.add-≅ (L.≅-refl⁰ _) (WT.coh (eN n) p q r)
  fl : ∀ n {x} → x L.≺ Bd n → ∀ {d} (p : d B.< B.suc (O (suc n))) → x L.≺ N′ n p
  fl zero h B.zero = ≺→⊑₀ (P≺ 0) h
  fl zero h (B.suc p) = add-left h _
  fl (suc n) h B.zero = lift≺ (P≺ (suc n)) h
  fl (suc n) h (B.suc p) = lift≺ (lead0 (P (suc n)) (proj₂ (V3m (f (suc (suc n))) (lf (suc (suc n)))) p)) h
  sp : ∀ n {x} → x L.≺ Bd n → x L.≺ read (F (G.lim f) (st , lf))
  sp zero h = L.≺l 0 h
  sp (suc n) h = L.≺l (suc (suc n)) (lift≺ (P≺ (suc n)) h)
  module BL = WT.Blk O Bd (read (F (G.lim f) (st , lf))) e₀ N′ Nb Nm Nc fl sp
  nzN : ∀ n {d} (p : d B.< B.suc (O (suc n))) → L.𝟎 {L.zero} L.≺ N′ n p
  nzN n B.zero = Pnz (suc n)
  nzN n (B.suc p) = add-left (Pnz n) _
  nzD : ∀ n {c} (m₀ : ∀ {c′} → c′ B.< BL.Σs n → T₀) → (∀ {c′} (q : c′ B.< BL.Σs n) → L.𝟎 {L.zero} L.≺ m₀ q) →
    (i : Inv (BL.Σs n) (B.suc (O (suc n))) c) → L.𝟎 {L.zero} L.≺ BL.disp n m₀ i
  nzD n m₀ h (inl q) = h q
  nzD n m₀ h (inr d r e) = nzN n r
  nzE : ∀ n {c} (p : c B.< BL.Σs n) → L.𝟎 {L.zero} L.≺ WT.map (BL.En n) p
  nzE zero p = proj₂ (V3m (f 0) (lf 0)) p
  nzE (suc n) p = nzD n (WT.map (BL.En n)) (nzE n) (inv {BL.Σs n} {B.suc (O (suc n))} p)
  nzL : ∀ {c} (p : c B.< ordᴰ (cp (G.lim f))) → L.𝟎 {L.zero} L.≺ WT.map BL.Lim p
  nzL (B.lim n p) = nzE n p

-- §4 链: 只带值序的不变量
emb : ∀ n m → D.γ n ≼ read (co (pts m)) → PEmb (D.L n) (κ (suc m))
emb n m w =
  PEmb-∘ (PW₃ (V1 (SV-L n)))
  (PEmb-∘ (PW₁ (V2′ (bkᴵ (N.L n)) (cp η) (St-bk (SV-L n)) (Mono-cp η l) w′))
  (PEmb-∘ (PW₂ (HS-read (obs (pts m)) (F-lgl η l)) (proj₁ (V3m η l)))
          (shift-κ m)))
  where
  η = co (pts m)
  l = lw (pts m)
  w′ : tr₀ (bkᴵ (N.L n)) ≼ tr₀ (cp η)
  w′ = ≼-trans (≅→≼ (bk≅γ n)) (≼-trans w (≅→≼ (L.≅-sym (cp≅ η))))

chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (co (pts m)))
chainV zero = 0 , ≼-refl _
chainV (suc n) = suc (suc m) ,
  ≼-trans (Ψ-emb (emb n m w))
    (plus≽ (co (pts (suc m))) (obs (pts (suc m))) (lower-read (co (pts (suc m))) (lw (pts (suc m)))))
  where
  m = proj₁ (chainV n)
  w = proj₂ (chainV n)

embT : EmbTⁿ
embT n = suc (proj₁ (chainV n)) , emb n (proj₁ (chainV n)) (proj₂ (chainV n))

btbo : D.BTBOᴵ ≼ read T₃
btbo = btbo-embⁿ embT

btbo⁺ : D.BTBOᴵ ≼ NA.read NT.T⁺
btbo⁺ = btbo-emb⁺ embT

-- 已发表的 BTBO (src, 累加在 ordᴰ 里) 经 BTBO≈ 换过来.
src-btbo⁺ : tr₀ S.BTBO ≼ NA.read NT.T⁺
src-btbo⁺ = ≼-trans (proj₁ BTBO≈) btbo⁺
```
