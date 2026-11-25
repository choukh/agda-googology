# 下一前缀的指定起点不满足 Le
不读记号；编译否定：第 2 前缀底更新中，指定两个非零层继承起点不满足 Le。
只否定这一加强的分量保持律，不否定值比较、ActualMissing、Offset 或 Cover。
Dry 受 YiTYNoDirect 的首位置读法启发，改查零层槽位；query-two 等式连接实际更新。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGSelf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVRRel as R
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiOGState as S
import OCF.Lean.YiOGFold as Fold
import OCF.Lean.YiOGTransfer as X

NZ : B.L → Set
NZ B.zero = ⊥
NZ (B.nd s h) = ⊤
Dry : (a : B.L) → B.Tr a → Set
Dry a B.zero = ⊤
Dry a (B.suc x) = Dry a x
Dry a (B.lim f b) = ∀ n → Dry a (f n)
Dry a (B.Ω p g) = NZ (B.at a p) × Dry a (g (B.fromBr a p B.zero))
Dry B.zero (B.up x () y e)
Dry (B.nd s h) (B.up x c y e) = Dry (B.nd s h) x × Dry (h c) y

down : ∀ {a x y} → R.Le a x y → Dry a y → Dry a x
down R.z≼ q = tt
down (R.s≼s d) q = down d q
down (R.≼s d) q = down d q
down (R.≼l n d) q = down d (q n)
down (R.l≼ h) q = λ n → down (h n) q
down (R.≼w d) q = down d (proj₂ q)
down {a} (R.w≼w {p = p} h) q = proj₁ q , down (h _ _ (R.fromBr≼ a p R.z≼)) (proj₂ q)
down {a = B.nd s h} (R.≼u d) q = down d (proj₁ q)
down {a = B.nd s h} (R.u≼u {c = c} dx dy) q = down dx (proj₁ q) , down {h c} dy (proj₂ q)

plus : ∀ a (x y : B.Tr a) → Dry a x → Dry a y → Dry a (x O.+ y)
plus a x B.zero q r = q
plus a x (B.suc y) q r = plus a x y q r
plus a x (B.lim f b) q r = λ n → plus a x (f n) q (r n)
plus a x (B.Ω p g) q r = proj₁ r , plus a x (g (B.fromBr a p B.zero)) q (proj₂ r)
plus B.zero x (B.up y () z e) q r
plus (B.nd s h) x (B.up y c z e) q r = plus (B.nd s h) x y q (proj₁ r) , proj₂ r
next : ∀ a (b : O.Tr⁺ a) → Dry a (proj₁ b) → Dry a (proj₁ (O.next⁺ b))
next a b q = go
  where
  go : (n : ℕ) → Dry a (O.iter (proj₁ b O.+_) (proj₁ b) n)
  go zero = q
  go (suc n) = plus a (proj₁ b) _ q (go n)

at-mv : ∀ {a j} (d : O.Dn a j) (p : B.Pos j) → B.at a (O.mv d p) ≡ B.at j p
at-mv O.stop p = refl
at-mv (O.down d c) p = at-mv d (inj₂ (c , inj₂ p))
up : ∀ {a} (j : B.L) (d : O.Dn a j) (b : O.Tr⁺ a) (y : B.Tr j)
  → Dry a (proj₁ b) → Dry j y → Dry a (proj₁ (O.Up j d b y))
up j d b B.zero q r = q
up {a} j d b (B.suc y) q r = next a (O.Up j d b y) (up j d b y q r)
up j d b (B.lim f a) q r = λ n → up j d b (f n) q (r n)
up j d b (B.Ω p g) q r = subst NZ (sym (at-mv d p)) (proj₁ r) ,
  up j d b (g (O.mvBr d p (B.fromBr _ (O.mv d p) B.zero))) q
    (subst (λ z → Dry j (g z)) (sym (O.mvFirst d p)) (proj₂ r))
up (B.nd s h) d b (B.up y c z e) q r = up (h c) (O.down d c) (O.Up (B.nd s h) d b y) z
  (up (B.nd s h) d b y q (proj₁ r)) (proj₂ r)

self : (a : B.L) (o : P.Ok a) (bs : F.Base a) (b : O.Tr⁺ a) (x : B.Tr a)
  → Dry a (proj₁ b) → Dry a x → Dry a (proj₁ (Fold.ψ a o bs a P.self b x))
self a o bs b B.zero q r = q
self a o bs b (B.suc x) q r = next a (Fold.ψ a o bs a P.self b x) (self a o bs b x q r)
self a o bs b (B.lim f adj) q r = λ n → self a o bs b (f n) q (r n)
self a o bs b (B.Ω p g) q r = proj₁ r , self a o bs b (g (B.fromBr a p B.zero)) q (proj₂ r)
self (B.nd s h) o bs b (B.up x c y e) q r = up (h c) (O.down O.stop c) (Fold.ψ (B.nd s h) o bs (B.nd s h) P.self b x) y
  (self (B.nd s h) o bs b x q (proj₁ r)) (proj₂ r)

one = C.g 0
two = C.g 1
three = C.h 0
omega-two : Dry two (proj₁ (O.Ωt two))
omega-two = tt , (tt , tt)
module High (o : P.Ok three) where
  oa = proj₂ o tt
  opaque
    tick : B.Tr two → B.Tr two
    tick c = proj₁ (O.next⁺ (Fold.ψ two oa (F.B₀ two) two P.self (O.Ωt two) c))
    tick-dry : ∀ c → Dry two c → Dry two (tick c)
    tick-dry c d = next two (Fold.ψ two oa (F.B₀ two) two P.self (O.Ωt two) c) (self two oa (F.B₀ two) (O.Ωt two) c omega-two d)
    value : O.Tr⁺ two
    value = Fold.ψ three o (F.B₀ three) two (P.inc tt P.self) (O.Ωt two) (proj₁ (O.Ωt three))
    value-row : proj₁ value ≡ proj₁ (O.limc⁺ (λ n → O.next⁺ (Fold.ψ two oa (F.B₀ two) two P.self
      (O.Ωt two) (O.iter tick B.zero n))))
    value-row = refl
  chain-dry : (n : ℕ) → Dry two (O.iter tick B.zero n)
  chain-dry zero = tt
  chain-dry (suc n) = tick-dry _ (chain-dry n)
  piece : ℕ → O.Tr⁺ two
  piece n = O.next⁺ (Fold.ψ two oa (F.B₀ two) two P.self (O.Ωt two) (O.iter tick B.zero n))
  piece-dry : ∀ n → Dry two (proj₁ (piece n))
  piece-dry n = next two (Fold.ψ two oa (F.B₀ two) two P.self (O.Ωt two) (O.iter tick B.zero n)) (self two oa (F.B₀ two) (O.Ωt two) (O.iter tick B.zero n) omega-two (chain-dry n))
  cum-dry : ∀ n → Dry two (O.cum (λ n → proj₁ (piece n)) n)
  cum-dry zero = piece-dry zero
  cum-dry (suc n) = plus two _ _ (cum-dry n) (piece-dry (suc n))
  value-dry : Dry two (proj₁ value)
  value-dry = subst (Dry two) (sym value-row) cum-dry
left = X.source-base two P.self
right = X.target-base two P.self
module Hi = High (proj₂ S.oh 0)
opaque
  unfolding S.G.base-at S.G.previous S.G.prefix S.G.part
  left-form : left ≡ O.Up one (O.down O.stop tt) (O.Ωt two) (proj₁ (O.Ωt one))
  left-form = refl
opaque
  unfolding S.T.base-at S.T.previous S.T.prefix S.T.part H.first H.curve H.line Hi.value
  right-form : right ≡ Hi.value
  right-form = refl
left-bad : Dry two (proj₁ left) → ⊥
left-bad d = proj₁ (subst (λ x → Dry two (proj₁ x)) left-form d)
right-dry : Dry two (proj₁ right)
right-dry = subst (λ x → Dry two (proj₁ x)) (sym right-form) Hi.value-dry
no-self-transfer : R.Le two (proj₁ left) (proj₁ right) → ⊥
no-self-transfer d = left-bad (down d right-dry)

source-carry : O.Tr⁺ two
source-carry = TB.ψ S.G.ℓ C.og (MT.rbᶻ S.G.ℓ) (F.B₀ S.G.ℓ) two
  (P.inc 2 (P.inc tt P.self)) (O.Ωt two) (S.G.prefix 0)
target-carry : O.Tr⁺ two
target-carry = TB.ψ S.T.ℓ S.oh (MT.rbᶻ S.T.ℓ) (F.B₀ S.T.ℓ) two
  (P.inc 2 (P.inc tt (P.inc tt (P.inc tt P.self)))) (O.Ωt two) (S.T.prefix 0)
opaque
  unfolding S.G.prefix S.G.part S.G.base-at S.G.previous
  source-carry-two : source-carry ≡ left
  source-carry-two = refl
opaque
  unfolding S.T.prefix S.T.part S.T.base-at S.T.previous H.first H.curve H.line
  target-carry-two : target-carry ≡ right
  target-carry-two = refl
no-carry-two : R.Le two (proj₁ source-carry) (proj₁ target-carry) → ⊥
no-carry-two d = no-self-transfer (subst₂ (λ x y → R.Le two (proj₁ x) (proj₁ y))
  source-carry-two target-carry-two d)

source-next : O.Tr⁺ two
source-next = TB.ψ (C.g 2) (proj₂ C.og 2) (MT.rbᶻ (C.g 2))
  (λ i u → TB.ψ S.G.ℓ C.og (MT.rbᶻ S.G.ℓ) (F.B₀ S.G.ℓ) i (P.inc 2 u) (O.Ωt i) (S.G.prefix 0))
  two (P.inc tt P.self) source-carry
  (proj₁ (P.emb (C.g 2) (proj₂ C.og 2) (P.self P.∙ proj₁ C.og 1) (O.Ωt (C.g 1))))
target-next : O.Tr⁺ two
target-next = TB.ψ (C.h 2) (proj₂ S.oh 2) (MT.rbᶻ (C.h 2))
  (λ i u → TB.ψ S.T.ℓ S.oh (MT.rbᶻ S.T.ℓ) (F.B₀ S.T.ℓ) i (P.inc 2 u) (O.Ωt i) (S.T.prefix 0))
  two (P.inc tt (P.inc tt (P.inc tt P.self))) target-carry
  (proj₁ (P.emb (C.h 2) (proj₂ S.oh 2) (P.self P.∙ proj₁ S.oh 1) (O.Ωt (C.h 1))))
opaque
  unfolding S.G.base-at S.G.previous S.G.prefix S.G.part
  source-query-two : S.G.base-at 2 two (P.inc tt P.self) ≡ source-next
  source-query-two = refl
opaque
  unfolding S.T.base-at S.T.previous S.T.prefix S.T.part
  target-query-two : S.T.base-at 2 two (P.inc tt (P.inc tt (P.inc tt P.self))) ≡ target-next
  target-query-two = refl
```
