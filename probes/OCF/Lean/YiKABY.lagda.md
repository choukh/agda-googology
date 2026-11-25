# 候选 A: 塔第 1 项那一层上以前缀折出的底, 折叠不低于 BTBO

> 验收文件, 树、折叠、合法性一行不改. 编译定理, 无前提: 层号 `tw 1` 上以 `BY` (左项是 `up zero zero 1` 的折叠) 为底的 Ω 树折叠, 经一致路径 (`β₂Y`) 或经任一孩子的路径 (`TY c w`), 读回都与 F2 上一个手造的底 `B‴` 的 `Fn 1 B‴` 同值 (`≅`); 后者由 `YiEBBtbo.btbo-B` 不低于 BTBO, 所以 `btbo-β₂Y`, `TY≅`.
> `BY` 在孩子 z 上的分量: 第 0 层是 `ω` (`BY0`), 其余层是孩子 z 的折叠在分支侧一行 (`φ`) 读出的嵌入树的折叠 (`BYN`); 这两条由证书切分 `cut` 的两个引理 (`cut0`, `cutN`) 得出. 第 0 层的树抄到 F2 (`τ₀`). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKABY where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiCertFold using (Base; node⁺; s+)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel hiding (RelE)
open import OCF.Lean.YiBRLem hiding (E→L; E-at; E-at⁼)
open import OCF.Lean.YiBROps hiding (emb-R; emb-mono-R)
open import OCF.Lean.YiBRFold using (W→L; iterR)
open import OCF.Lean.YiBRTw using (↑-L)
open import OCF.Lean.YiKARel
open import OCF.Lean.YiKATw1 using (h₁ᴷ; o₁; ab-W)
open import OCF.Lean.YiKAMono using (νc)
open import OCF.Lean.YiVRRel using (NoΩ; NoΩ↑)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Lean.YiLSFold using (OKB; ψs-⊵)
open import OCF.Lean.YiLSRead using (read; _⊢_⊴_; ⊴r; ⊴◃)
open import OCF.Lean.YiEBShape using (Fn)
open import OCF.Lean.YiEBBtbo using (Start; module Chain; module Btbo)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 第 0 层的树抄到 F2

```agda
mutual
  τ₀ : Tr zero → F.Tr F.zero
  τ₀ zero         = F.zero
  τ₀ (suc x)      = F.suc (τ₀ x)
  τ₀ (lim f a)    = F.lim (λ n → τ₀ (f n)) (λ n → τ◃ (a n))
  τ₀ (Ω () g)
  τ₀ (up x () y e)

  τ◃ : {x y : Tr zero} → zero ⊢ x ◃ y → F._⊢_◃_ F.zero (τ₀ x) (τ₀ y)
  τ◃ ◃s            = F.◃s
  τ◃ (◃l n)        = F.◃l n
  τ◃ (◃t d e)      = F.◃t (τ◃ d) (τ◃ e)
  τ◃ (◃w {p = ()})
  τ◃ (◃u x () y e)
  τ◃ (◃c x () r)

mutual
  τ₀-R : (x : Tr zero) → RelT zero F.zero x (τ₀ x)
  τ₀-R zero          = iz
  τ₀-R (suc x)       = is (τ₀-R x)
  τ₀-R (lim f a)     = il ((λ n → τ₀-R (f n)) , (λ n → τ◃-R (a n)))
  τ₀-R (Ω () g)
  τ₀-R (up x () y e)

  τ◃-R : {x y : Tr zero} (d : zero ⊢ x ◃ y) → RelD zero F.zero d (τ◃ d)
  τ◃-R ◃s            = ds
  τ◃-R (◃l n)        = dl
  τ◃-R (◃t d e)      = dt (τ◃-R d , τ◃-R e)
  τ◃-R (◃w {p = ()})
  τ◃-R (◃u x () y e)
  τ◃-R (◃c x () r)
```

## 证书切分的两个引理

目标是第 0 层且源层号不含 Ω 形状时切到地板 (`cut0`); 目标在地板以上时不切 (`cutN`).

```agda
cut0 : ∀ {m} (U : Ab zero m) (w : zero ≤ m) → NoΩ m → cut U w ≡ inj₁ self
cut0 here   self      ν = refl
cut0 (ab f) (inc c v) ν = cut0 (f c) v (νc ν c)
cut0 {m = nd s h} (ab f) (inu vs) ν = cut0 (f (c₀ s)) (vs (c₀ s)) (νc ν (c₀ s))
cut0 (ab f) (ink v)   ()

cutN : ∀ {m s h} (U : Ab zero m) (w : nd s h ≤ m) → cut U w ≡ inj₂ tt
cutN (ab f) self      = refl
cutN (ab f) (inc c v) = cutN (f c) v
cutN {m = nd s′ h′} (ab f) (inu vs) = cutN (f (c₀ s′)) (vs (c₀ s′))
cutN (ab f) (ink v)   = refl

cW-R₁ : ∀ {A B X : Set} (P : X → Set) (W : A ⊎ B) {a : A} → W ≡ inj₁ a → {F : A → X} {G : B → X} → P (F a) → P (cW W F G)
cW-R₁ P .(inj₁ _) refl p = p

cW-R₂ : ∀ {A B X : Set} (P : X → Set) (W : A ⊎ B) {b : B} → W ≡ inj₂ b → {F : A → X} {G : B → X} → P (G b) → P (cW W F G)
cW-R₂ P .(inj₂ _) refl p = p
```

## 底 `BY` 与它在孩子上的分量

```agda
Y : Tr (tw 1)
Y = up zero zero (suc zero) ◃s

BY : Base (tw 1)
BY i u = ψ (tw 1) o₁ (λ i′ u′ → Ωt i′) i u (Ωt i) Y

ω : Tr⁺ zero
ω = next⁺ (Ωt zero)

ω-ink : BY zero (ink self) ≡ ω
ω-ink = refl

BY0 : (z : Tr zero) (w : zero ≤ h₁ᴷ z) → BY zero (inc z w) ≡ ω
BY0 z w = cW-R₁ (λ X → X ≡ ω) (cut (crt o₁ z) w) (cut0 (crt o₁ z) w (NoΩ↑ z)) refl

Ez : (z : Tr zero) → Tr⁺ (h₁ᴷ z)
Ez z = emb (h₁ᴷ z) (proj₂ o₁ z) (ab→≤ (crt o₁ z)) (s+ (suc zero))
```

## F2 上的底 `B‴`

```agda
ω′ : F.Tr F.zero
ω′ = F.next (F.Ωt F.zero) (F.Ωt-nz F.zero)

nω′ : F._⊢_◃_ F.zero F.zero ω′
nω′ = F.◃t (F.Ωt-nz F.zero) (F.◃l zero)

E′ : (z′ : F.Tr F.zero) → F.Tr (T1.h₁ z′)
E′ z′ = F.emb (T1.h₁ z′) (T1.εh z′) (F.lift F.zero (F.↑ F.zero z′)) (F.suc (F.suc F.zero)) (F.z◃s (F.suc F.zero))

bsY′ : (z′ : F.Tr F.zero) (j′ : F.L) → F._≤_ j′ (T1.h₁ z′) → F.Tr j′
bsY′ z′ F.zero w′ = ω′
bsY′ z′ j′     w′ = F.ψs (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) j′ w′ (F.Ωt j′) (F.Ωt-nz j′) (E′ z′)

nsY′ : (z′ : F.Tr F.zero) (j′ : F.L) (w′ : F._≤_ j′ (T1.h₁ z′)) → F._⊢_◃_ j′ F.zero (bsY′ z′ j′ w′)
nsY′ z′ F.zero         w′ = nω′
nsY′ z′ (F.suc a)      w′ = F.nzs (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) (F.suc a) w′ (F.Ωt (F.suc a)) (F.Ωt-nz (F.suc a)) (E′ z′)
nsY′ z′ (F.lim g)      w′ = F.nzs (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) (F.lim g) w′ (F.Ωt (F.lim g)) (F.Ωt-nz (F.lim g)) (E′ z′)
nsY′ z′ (F.Ωₗ k h)     w′ = F.nzs (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) (F.Ωₗ k h) w′ (F.Ωt (F.Ωₗ k h)) (F.Ωt-nz (F.Ωₗ k h)) (E′ z′)

dflt : (j′ : F.L) → F.Tr j′
dflt F.zero = ω′
dflt j′     = F.Ωt j′

ndflt : (j′ : F.L) → F._⊢_◃_ j′ F.zero (dflt j′)
ndflt F.zero     = nω′
ndflt (F.suc a)  = F.Ωt-nz (F.suc a)
ndflt (F.lim g)  = F.Ωt-nz (F.lim g)
ndflt (F.Ωₗ k h) = F.Ωt-nz (F.Ωₗ k h)

bs‴ : (j′ : F.L) → F._≤_ j′ (F.tw 1) → F.Tr j′
bs‴ j′ (F.inb z′ w′) = bsY′ z′ j′ w′
bs‴ j′ w′            = dflt j′

ns‴ : (j′ : F.L) (w′ : F._≤_ j′ (F.tw 1)) → F._⊢_◃_ j′ F.zero (bs‴ j′ w′)
ns‴ j′ (F.inb z′ w′) = nsY′ z′ j′ w′
ns‴ j′ F.self        = ndflt j′
ns‴ j′ (F.ink w′)    = ndflt j′
ns‴ j′ (F.inu ws)    = ndflt j′

B‴ : F.Base (F.tw 1)
B‴ = F.base ω′ nω′ bs‴ ns‴
```

## `B‴` 满足 `OKB` 与起点条件, 所以不低于 BTBO

```agda
okD : (j′ : F.L) → j′ ⊢ F.Ωt j′ ⊴ dflt j′
okD F.zero     = ⊴◃ (F.◃l zero)
okD (F.suc a)  = ⊴r
okD (F.lim g)  = ⊴r
okD (F.Ωₗ k h) = ⊴r

okY : (z′ : F.Tr F.zero) (j′ : F.L) (w′ : F._≤_ j′ (T1.h₁ z′)) → j′ ⊢ F.Ωt j′ ⊴ bsY′ z′ j′ w′
okY z′ F.zero     w′ = ⊴◃ (F.◃l zero)
okY z′ (F.suc a)  w′ = ψs-⊵ (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) (F.suc a) w′ (F.Ωt (F.suc a)) (F.Ωt-nz (F.suc a)) (E′ z′)
okY z′ (F.lim g)  w′ = ψs-⊵ (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) (F.lim g) w′ (F.Ωt (F.lim g)) (F.Ωt-nz (F.lim g)) (E′ z′)
okY z′ (F.Ωₗ k h) w′ = ψs-⊵ (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (F.B₀ (T1.h₁ z′)) (F.Ωₗ k h) w′ (F.Ωt (F.Ωₗ k h)) (F.Ωt-nz (F.Ωₗ k h)) (E′ z′)

ok‴ : OKB (F.tw 1) B‴
ok‴ = ⊴◃ (F.◃l zero) , go
  where
  go : (j′ : F.L) (w′ : F._≤_ j′ (F.tw 1)) → j′ ⊢ F.Ωt j′ ⊴ bs‴ j′ w′
  go j′ (F.inb z′ w′) = okY z′ j′ w′
  go j′ F.self        = okD j′
  go j′ (F.ink w′)    = okD j′
  go j′ (F.inu ws)    = okD j′

E-reflF : (x : F.Tr F.zero) → T1.E x x
E-reflF F.zero          = T1.ez
E-reflF (F.suc x)       = T1.es (E-reflF x)
E-reflF (F.lim f a)     = T1.el (λ n → E-reflF (f n))
E-reflF (F.Ω () g)
E-reflF (F.up x () y e)

st‴ : Start B‴
st‴ = E-reflF ω′

btbo‴ : D.BTBOᴵ ≼ read (Fn 1 B‴)
btbo‴ = Btbo.btbo-B B‴ ok‴ st‴
```

## 孩子 z 上的底相关

```agda
module C‴ = Chain B‴

rω : RelT zero F.zero (proj₁ ω) ω′ × RelD zero F.zero (proj₂ ω) nω′
rω = next-R (Ωt zero) (Ωt-R lz) (Ωn-R lz)

rEz : {z : Tr zero} {z′ : F.Tr F.zero} (r : RelT zero F.zero z z′)
    → RelT (h₁ᴷ z) (T1.h₁ z′) (proj₁ (Ez z)) (E′ z′)
rEz r = proj₁ (embK-R (h₁-EK r) (ab-W (↑-L lz r)) (s+ (suc zero)) (is (is iz)) (zs-R lz (is iz)))

rBY : (z : Tr zero) (z′ : F.Tr F.zero) (r : RelT zero F.zero z z′)
    → RelBase (h₁ᴷ z) (T1.h₁ z′) (λ i u → BY i (inc z u)) (C‴.Bc z′)
rBY z z′ r j j′ w w′ rw = go (W→L (E→LK (h₁-EK r)) rw) w′ rw
  where
  re = h₁-EK r
  P0 : Tr⁺ zero → Set
  P0 t = RelT zero F.zero (proj₁ t) ω′ × RelD zero F.zero (proj₂ t) nω′
  go : {j : L} {j′ : F.L} → RelL j j′ → {w : j ≤ h₁ᴷ z} (w′ : F._≤_ j′ (T1.h₁ z′)) → RelW w w′
     → RelT j j′ (proj₁ (BY j (inc z w))) (bsY′ z′ j′ w′) × RelD j j′ (proj₂ (BY j (inc z w))) (nsY′ z′ j′ w′)
  go lz {w} w′ rw = subst P0 (sym (BY0 z w)) rω
  go rj@(lS _) {w} w′ rw =
    cW-R₂ (λ X → RelT _ _ (proj₁ X) (bsY′ z′ _ w′) × RelD _ _ (proj₂ X) (nsY′ z′ _ w′)) (cut (crt o₁ z) w) (cutN (crt o₁ z) w)
      (SK re (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK re)) rw (Ωt _) (Ωt-R rj) (Ωn-R rj) (rEz r))
  go rj@(lL _) {w} w′ rw =
    cW-R₂ (λ X → RelT _ _ (proj₁ X) (bsY′ z′ _ w′) × RelD _ _ (proj₂ X) (nsY′ z′ _ w′)) (cut (crt o₁ z) w) (cutN (crt o₁ z) w)
      (SK re (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK re)) rw (Ωt _) (Ωt-R rj) (Ωn-R rj) (rEz r))
  go rj@(lΩ _ _) {w} w′ rw =
    cW-R₂ (λ X → RelT _ _ (proj₁ X) (bsY′ z′ _ w′) × RelD _ _ (proj₂ X) (nsY′ z′ _ w′)) (cut (crt o₁ z) w) (cutN (crt o₁ z) w)
      (SK re (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK re)) rw (Ωt _) (Ωt-R rj) (Ωn-R rj) (rEz r))
```

## 链

```agda
sY : Tr zero → Tr zero
sY z = proj₁ (ψ (h₁ᴷ z) (proj₂ o₁ z) (λ i u → BY i (inc z u)) zero (self ∙ kh o₁ z) ω (proj₁ (Ωt (h₁ᴷ z))))

rsY : (z : Tr zero) (z′ : F.Tr F.zero) (r : RelT zero F.zero z z′) → RelT zero F.zero (sY z) (C‴.K z′)
rsY z z′ r = proj₁ (SK (h₁-EK r) (λ i u → BY i (inc z u)) (C‴.Bc z′) (rBY z z′ r)
  (∙-R wself (idl-R (ab-W (↑-L lz r)))) ω (proj₁ rω) (proj₂ rω) (Ωt-R (E→LK (h₁-EK r))))

chY : (n : ℕ) → RelT zero F.zero (iter sY zero n) (C‴.pt n)
chY = iterR (RelT zero F.zero) iz rsY
```

## 经一致路径: `β₂Y`

```agda
β₂Y : Tr⁺ zero
β₂Y = ψ (tw 1) o₁ BY zero (z≤ (tw 1)) ω (proj₁ (Ωt (tw 1)))

GYz : Tr zero → Tr⁺ zero
GYz z = ψ (h₁ᴷ z) (proj₂ o₁ z) (λ i u → BY i (inc z u)) zero (z≤ (h₁ᴷ z)) ω (proj₁ (Ωt (h₁ᴷ z)))

formβ : proj₁ β₂Y ≡ proj₁ (limc⁺ (λ n → GYz (iter sY zero n)))
formβ = refl

β₂Y-R : RelT zero F.zero (proj₁ β₂Y) (Fn 1 B‴)
β₂Y-R = limc-R (λ n → GYz (iter sY zero n)) (λ n → proj₁ (rG (chY n))) (λ n → proj₂ (rG (chY n)))
  where
  rG : {z : Tr zero} {z′ : F.Tr F.zero} (r : RelT zero F.zero z z′)
     → RelT zero F.zero (proj₁ (GYz z)) (C‴.G z′) × RelD zero F.zero (proj₂ (GYz z)) (C‴.G-nz z′)
  rG {z} {z′} r = AK (h₁-EK r) (λ i u → BY i (inc z u)) (C‴.Bc z′) (rBY z z′ r) ω (proj₁ rω) (proj₂ rω) (Ωt-R (E→LK (h₁-EK r)))

btbo-β₂Y : D.BTBOᴵ ≼ readRW (proj₁ β₂Y)
btbo-β₂Y = ≼-trans btbo‴ (≅→≼ (L.≅-sym (rel≅ β₂Y-R)))
```

## 经孩子 c 的路径: `TY c w`

结点在第 0 层不保留 (`node0K`); 每一行的证书切到地板, 是孩子 z 上以 `lift` 形路径的折叠, 与 F2 的链点 `K` 相关; F2 一侧 `K` 与 `G` 逐点同形 (`T1.eq0`).

```agda
TY : (c : Tr zero) → zero ≤ h₁ᴷ c → Tr⁺ zero
TY c w = ψ (tw 1) o₁ BY zero (inc c w) (BY zero (inc c w)) (proj₁ (Ωt (tw 1)))

T″ : F.Tr F.zero
T″ = F.limc (λ n → C‴.K (C‴.pt n))
  (λ n → F.nzs (T1.h₁ (C‴.pt n)) (T1.εh (C‴.pt n)) (T1.ρh (C‴.pt n)) (C‴.Bc (C‴.pt n)) F.zero (T1.wh (C‴.pt n)) ω′ nω′ (F.Ωt (T1.h₁ (C‴.pt n))))

TY-R : (c : Tr zero) (w : zero ≤ h₁ᴷ c)
     → RelT zero F.zero (proj₁ (TY c w)) T″
TY-R c w = proj₁ (node0K (kp (tw 1) o₁ (inj₁ (inj₁ tt)) (inc c w)) Gw sY
  (limc-R (λ n → Gw (iter sY zero n)) (λ n → proj₁ (rG (chY n))) (λ n → proj₂ (rG (chY n)))
   , dt (proj₂ (rG (chY zero)) , dl)))
  where
  Gw : Tr zero → Tr⁺ zero
  Gw z = ψ (tw 1) o₁ BY zero (inc c w) (BY zero (inc c w)) (proj₁ (upz {s = sΩ zero} {h = h₁ᴷ} z (Ωt (h₁ᴷ z))))
  rβ : RelT zero F.zero (proj₁ (BY zero (inc c w))) ω′ × RelD zero F.zero (proj₂ (BY zero (inc c w))) nω′
  rβ = subst (λ t → RelT zero F.zero (proj₁ t) ω′ × RelD zero F.zero (proj₂ t) nω′) (sym (BY0 c w)) rω
  rG : {z : Tr zero} {z′ : F.Tr F.zero} (r : RelT zero F.zero z z′)
     → RelT zero F.zero (proj₁ (Gw z)) (C‴.K z′)
     × RelD zero F.zero (proj₂ (Gw z)) (F.nzs (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (C‴.Bc z′) F.zero (T1.wh z′) ω′ nω′ (F.Ωt (T1.h₁ z′)))
  rG {z} {z′} r =
    cW-R₁ (λ X → RelT zero F.zero (proj₁ X) (C‴.K z′)
               × RelD zero F.zero (proj₂ X) (F.nzs (T1.h₁ z′) (T1.εh z′) (T1.ρh z′) (C‴.Bc z′) F.zero (T1.wh z′) ω′ nω′ (F.Ωt (T1.h₁ z′))))
      (cut (crt o₁ c) w) (cut0 (crt o₁ c) w (NoΩ↑ c))
      (SK (h₁-EK r) (λ i u → BY i (inc z u)) (C‴.Bc z′) (rBY z z′ r)
        (∙-R wself (ab-W (↑-L lz r))) (BY zero (inc c w)) (proj₁ rβ) (proj₂ rβ) (Ωt-R (E→LK (h₁-EK r))))

T″E : T1.E T″ (Fn 1 B‴)
T″E = T1.E-cum (λ n → C‴.K (C‴.pt n)) (λ n → C‴.G (C‴.pt n))
  (λ n → T1.eq0 (T1.h₁ (C‴.pt n)) (T1.εh (C‴.pt n)) (T1.ρh (C‴.pt n)) (C‴.Bc (C‴.pt n)) (T1.wh (C‴.pt n))
           (T1.LiftP-∙ F.zero (F.↑ F.zero (C‴.pt n)) F.self tt) ω′ nω′ (E-reflF ω′) (F.Ωt (T1.h₁ (C‴.pt n))))

TY≅ : (c : Tr zero) (w : zero ≤ h₁ᴷ c) → readRW (proj₁ (TY c w)) L.≅ readRW (proj₁ β₂Y)
TY≅ c w = L.≅-trans (rel≅ (TY-R c w)) (L.≅-trans (T1.E→≅ T″E) (L.≅-sym (rel≅ β₂Y-R)))
```
