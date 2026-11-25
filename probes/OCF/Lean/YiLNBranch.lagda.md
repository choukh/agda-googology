# 冻结接口的配对否定 (一): 分支侧同支交接

> 验收文件 (否定), 编译定理. 候选字段 `J2-Ωb` (Ω 结点层号上目标 `inb c w` 与嵌入 `up x c y` 同支时交给孩子) 加异支的头部不是结点 (`Offᴴ`; 回退式 `Ωb-off` 蕴含它, `legI` 满足), 对 `Iface` 的任何实例弱判定塔第 3 项的下标 c₀ 与一切 c′ 的字面相等 (`wdec`, 经 `hand→wdec`); 加 ℕ → Bool 上的函数外延得 WLPO (`wlpo`, 条件定理); 经同支证据派发 (`ViaE`, `legI` 满足) 则判等 (`viaE→dec`, 经 `RowLaws.viaE→dec`).
> 合法块上的探针 `probeᴸ`, `offᴸ` 补上 `YiAbsLeg.leg-wdec` 缺的前提 (`leg-wdec-tw3`); `legI` 不满足 `J2-Ωb` (`legI-not-J2Ωb`). 探针在规范域: 塔第 3 项, 证据 `Ev-tw 3`, 路线 `Rt-tw 3`, 下标 c₀, cα α 是它的分支.
> 不否定什么: 一致目标 (`J2-Ωu`), 自身行, 接口本身. 重推 `YiPhiNegB.wdec`, `wlpo`, `viaE→dec` 到合法块与冻结接口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLNBranch where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (_+_; ι; Ωt; Ωt-nz; ¬◃z)
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (Base; B₀)
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiLPIface using (Iface)
open import OCF.Lean.YiLPInst using (legI)
open import OCF.Lean.YiAbsObs using (WDec; Dec′; Sep; Cantor; AllF; WLPO; t≢f; sep→wlpo; Row; module RowLaws)
open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsLeg using (blkᴸ; hdΩ; Bsᴸ; Btᴸ; foldᴸ; leg-wdec)
```

## 候选字段

```agda
J2-Ωb : Iface → Set
J2-Ωb I = let open Iface I in
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c : Tr k) (w : j ≤ h c)
  (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (up x c y e)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j w
      (ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c w) β nβ x) y

Offᴴ : Iface → Set
Offᴴ I = let open Iface I in
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → (c ≡ c′ → ⊥) → hdΩ (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)) ≡ false

Ωb-off : Iface → Set
Ωb-off I = let open Iface I in
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → (c ≡ c′ → ⊥)
  → ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
  ≡ ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y)

handL : ∀ {k} {h : Tr k → L} {j} {c c′ : Tr k} → c ≡ c′ → j ≤ h c′ → j ≤ h c
handL refl w = w

ViaE : Iface → Set
ViaE I = let open Iface I in
  Σ ((k : L) (c c′ : Tr k) → Maybe (c ≡ c′)) λ E →
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
  ≡ maybe′ (λ q → ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (handL {h = h} q w)
                     (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) y)
           (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y))
           (E k c c′)
```

## 回退的头部; 前提的实例

```agda
plus-ι : ∀ {j} (a : Tr j) (t : Tr zero) → zero ⊢ zero ◃ t → hdΩ (a + ι j t) ≡ false
plus-ι a zero          nz = ⊥-elim (¬◃z nz)
plus-ι a (suc t)       nz = refl
plus-ι a (lim f s)     nz = refl
plus-ι a (Ω () g)      nz
plus-ι a (up y () z e) nz

off→offᴴ : (I : Iface) → Ωb-off I → Offᴴ I
off→offᴴ I O k h ε ρ B j c c′ w β nβ x y e ne =
  trans (cong hdΩ (O k h ε ρ B j c c′ w β nβ x y e ne))
        (plus-ι _ _ (Iface.nz⊥ I (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y))

off-legI : Ωb-off legI
off-legI k h ε ρ B j c c′ w β nβ x y e ne = refl

offᴴ-legI : Offᴴ legI
offᴴ-legI = off→offᴴ legI off-legI

viaE-legI : ViaE legI
viaE-legI = (λ _ _ _ → nothing) , λ k h ε ρ B j c c′ w β nβ x y e → refl
```

`J2-Ωb` 的式子单独可满足: 常值折叠 (输出恒为偏移) 满足它; 它不是接口实例 (不严格单调).

```agda
J2-Ωbᶠ : (ψs : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j)
  (nzs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
       → j ⊢ zero ◃ ψs ℓ ε ρ B j w β nβ x)
  (dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Rt (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c))
  → Set
J2-Ωbᶠ ψs nzs dW =
  (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c : Tr k) (w : j ≤ h c)
  (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (up x c y e)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j w
      (ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c w) β nβ x) y

j2b-const : J2-Ωbᶠ (λ ℓ ε ρ B j w β nβ x → β) (λ ℓ ε ρ B j w β nβ x → nβ) (λ k h ε ρ B c x → B₀ (h c))
j2b-const k h ε ρ B j c w β nβ x y e = refl
```

## 探针: 塔第 3 项, 目标 tw 1 在分支 c′ 里

c₀ 的第 m 项是 2m 个后继; cα α 在 α m 为真处多一个后继, c₀ 就是 cα 在常假序列上的值 (于是函数外延只用于 ℕ → Bool). 嵌入的树在 c₀ 的第 0 项 (层号 tw 2) 里, 是 tw 2 第 0 个孩子里的顶槽位结点.

```agda
sucs : ∀ {S} → ℕ → T S
sucs zero    = zero
sucs (suc m) = suc (sucs m)

double : ℕ → ℕ
double zero    = zero
double (suc m) = suc (suc (double m))

ev : ℕ → Tr (tw 2)
ev m = sucs (double m)

bump : ∀ {S} → Bool → T S → T S
bump true  t = suc t
bump false t = t

bstep : ∀ {S} (a b : Bool) (t : T S) → Lt S (bump a t) (bump b (suc (suc t)))
bstep true  true  t = ◃t ◃s ◃s
bstep true  false t = ◃s
bstep false true  t = ◃t ◃s (◃t ◃s ◃s)
bstep false false t = ◃t ◃s ◃s

cF : (ℕ → Bool) → ℕ → Tr (tw 2)
cF α m = bump (α m) (ev m)

cα : (ℕ → Bool) → Tr (tw 2)
cα α = lim (cF α) (λ m → bstep (α m) (α (suc m)) (ev m))

c₀ : Tr (tw 2)
c₀ = cα (λ _ → false)

h₃ : Tr (tw 2) → L
h₃ c = tw 2 ⊕ ↑ (tw 2) c

wc : (c : Tr (tw 2)) → tw 1 ≤ h₃ c
wc c = ink self ∙ lift (tw 2) (↑ (tw 2) c)

top₁ : Pos (tw 1)
top₁ = inj₁ (inj₁ tt)

y₁ : Tr (tw 2)
y₁ = up zero zero (Ω top₁ (λ _ → zero)) ◃w

e₁ : tw 2 ⊢ zero ◃ y₁
e₁ = ◃u zero zero (Ω top₁ (λ _ → zero)) ◃w

y₀ : Tr (h₃ c₀)
y₀ = up zero zero y₁ e₁

e₀ : h₃ c₀ ⊢ zero ◃ y₀
e₀ = ◃u zero zero y₁ e₁

b₃ : Bsᴸ (tw 3)
b₃ = Ev-tw 3 , Rt-tw 3 , B₀ (tw 3)

β₁ : Btᴸ (tw 1)
β₁ = Ωt (tw 1) , Ωt-nz (tw 1)
```

c₀ ≡ cα α 推出 α 处处为假; 反方向只要 ℕ → Bool 上的函数外延.

```agda
comp : Tr (tw 2) → ℕ → Tr (tw 2)
comp (lim f _) = f
comp _         = λ _ → zero

pd : Tr (tw 2) → Tr (tw 2)
pd (suc t) = t
pd t       = t

no-suc : (m : ℕ) → sucs {Sig (tw 2)} m ≡ suc (sucs m) → ⊥
no-suc zero    ()
no-suc (suc m) e = no-suc m (cong pd e)

eq→allF : ∀ α → c₀ ≡ cα α → AllF α
eq→allF α e n = go (α n) (cong (λ t → comp t n) e)
  where
  go : (b : Bool) → ev n ≡ bump b (ev n) → b ≡ false
  go true  e′ = ⊥-elim (no-suc (double n) e′)
  go false e′ = refl

cantor : Cantor c₀
cantor = record { cα = cα ; eq→allF = eq→allF }

Funext₀ : Set
Funext₀ = {f g : ℕ → Bool} → ((n : ℕ) → f n ≡ g n) → f ≡ g

allF→eq : Funext₀ → ∀ α → AllF α → c₀ ≡ cα α
allF→eq fe α af = cong cα (fe (λ n → sym (af n)))
```

## 任何接口实例填进框架; 否定

```agda
module Frame (I : Iface) where
  open Iface I

  dnI : (ℓ : L) → Bsᴸ ℓ → (c : Ch ℓ) → Tr ℓ → Bsᴸ (chL ℓ c)
  dnI zero     b           () x
  dnI (suc a)  (ε , ρ , B) _  x = ε , ρ , dS a ε ρ B x
  dnI (lim g)  (ε , ρ , B) n  x = ε n , proj₁ ρ n , dL g ε ρ B n x
  dnI (Ωₗ k h) (ε , ρ , B) c  x = proj₂ (proj₂ ε c) , proj₂ ρ c , dW k h ε ρ B c x

  foldI : Fold blkᴸ
  foldI = record
    { Bs   = Bsᴸ
    ; LegB = λ _ _ → ⊤
    ; Bt   = Btᴸ
    ; LegT = λ _ _ → ⊤
    ; ψ    = λ ℓ b j w β x → ψs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w (proj₁ β) (proj₂ β) x
    ; ψβ   = λ ℓ b j w β x → ψs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w (proj₁ β) (proj₂ β) x
                           , nzs ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) j w (proj₁ β) (proj₂ β) x
    ; dn   = dnI }

  hand-Ω : J2-Ωb I → (k : L) (h : Tr k → L) → Fold.Hand foldI (Ωₗ k h)
  hand-Ω J k h (ε , ρ , B) j c w (β , nβ) x (y , e) = J k h ε ρ B j c w β nβ x y e
```

`on`: 接口的 `J2-limu` (孩子层 h₃ c₀ 是 ℕ 极限, 路径 `wc c₀` 是 `inlu`) 接 `kstep` (第 0 项是 `Nx (tw 1)`, 顶槽位结点原样保留).

```agda
  probe : Fold.Probe foldI (tw 3)
  probe = record
    { b = b₃ ; j = tw 1 ; β = β₁ ; x = zero ; c₀ = c₀ ; y = y₀ , e₀ ; w = wc
    ; on = cong hdΩ (trans (J2-limu (λ m → h₃ (cF (λ _ → false) m)) (proj₂ (proj₂ (Ev-tw 3) c₀))
                                    (proj₂ (Rt-tw 3) c₀) _ (tw 1) (λ m → wc (cF (λ _ → false) m)) _ _ zero zero y₁ e₁)
                           (kstep (tw 1) (Ev-tw 1) (Rt-tw 1) _ _ _ zero top₁ (λ _ → zero) ◃w)) }

  offᴾ : Offᴴ I → Fold.Offᴾ foldI probe
  offᴾ O c′ ne = O (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) c₀ c′ (wc c′) (Ωt (tw 1)) (Ωt-nz (tw 1))
                   zero y₀ e₀ ne

  wdec : J2-Ωb I → Offᴴ I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
  wdec J O = Fold.hand→wdec foldI (hand-Ω J (tw 2) h₃) probe (offᴾ O)

  wlpo : Funext₀ → J2-Ωb I → Offᴴ I → WLPO
  wlpo fe J O = sep→wlpo (Fold.hand→sep foldI (hand-Ω J (tw 2) h₃) probe (offᴾ O)) cantor (allF→eq fe)
```

经同支证据派发: 这一行是 `rowOf` 的实例, 回退 `fbᴿ` 的头部恒假, 由 `RowLaws.viaE→dec` 判等.

```agda
  fbᴿ : (c′ : Tr (tw 2)) → tw 1 ≤ h₃ c′ → (c : Tr (tw 2)) → Σ (Tr (h₃ c)) (λ y → h₃ c ⊢ zero ◃ y) → Tr (tw 1)
  fbᴿ c′ w c (y , e) = ψs (tw 3) (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) (inb c′ w) (Ωt (tw 1)) (Ωt-nz (tw 1)) zero
                     + ι (tw 1) (ψ⊥ (h₃ c) (proj₂ (proj₂ (Ev-tw 3) c)) (proj₂ (Rt-tw 3) c) (B₀ (h₃ c)) y)

  viaE→dec : J2-Ωb I → ViaE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)
  viaE→dec J (E , V) = RowLaws.viaE→dec Rw rw Sw (E (tw 2) , V′) Pw
    where
    Rw = Fold.rowOf foldI (tw 3) b₃ (tw 1) β₁ zero fbᴿ
    rw = Fold.disp foldI (tw 3) b₃ (tw 1) β₁ zero
    Sw = Fold.hand→same foldI (hand-Ω J (tw 2) h₃) b₃ (tw 1) β₁ zero fbᴿ
    agree : (c′ : Tr (tw 2)) (w : tw 1 ≤ h₃ c′) (c : Tr (tw 2)) (ye : Σ (Tr (h₃ c)) (λ y → h₃ c ⊢ zero ◃ y))
      (m : Maybe (c ≡ c′))
      → maybe′ (λ q → ψs (h₃ c) (proj₂ (proj₂ (Ev-tw 3) c)) (proj₂ (Rt-tw 3) c)
                         (dW (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) c zero) (tw 1) (handL {h = h₃} q w)
                         (ψs (tw 3) (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) (inb c′ w) (Ωt (tw 1)) (Ωt-nz (tw 1)) zero)
                         (nzs (tw 3) (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) (inb c′ w) (Ωt (tw 1)) (Ωt-nz (tw 1)) zero)
                         (proj₁ ye))
               (fbᴿ c′ w c ye) m
      ≡ maybe′ (λ q → Row.k Rw c (RowLaws.hand Rw q w) ye) (fbᴿ c′ w c ye) m
    agree c′ w c ye (just refl) = refl
    agree c′ w c ye nothing     = refl
    V′ : (c′ : Tr (tw 2)) (w : tw 1 ≤ h₃ c′) (c : Tr (tw 2)) (ye : Σ (Tr (h₃ c)) (λ y → h₃ c ⊢ zero ◃ y))
      → rw c′ w c ye ≡ maybe′ (λ q → Row.k Rw c (RowLaws.hand Rw q w) ye) (fbᴿ c′ w c ye) (E (tw 2) c c′)
    V′ c′ w c (y , e) = trans (V (tw 2) h₃ (Ev-tw 3) (Rt-tw 3) (B₀ (tw 3)) (tw 1) c c′ w (Ωt (tw 1)) (Ωt-nz (tw 1))
                                 zero y e)
                              (agree c′ w c (y , e) (E (tw 2) c c′))
    Pw : RowLaws.Probe Rw
    Pw = record { c₀ = c₀ ; w = wc ; y = y₀ , e₀ ; k-on = Fold.Probe.on probe
               ; fb-off = λ c′ → plus-ι _ _ (nz⊥ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (proj₂ (Rt-tw 3) c₀) (B₀ (h₃ c₀)) y₀) }
```

## 合法块自身: 补上 `leg-wdec` 的探针; `legI` 不满足 `J2-Ωb`

```agda
probeᴸ : Fold.Probe foldᴸ (tw 3)
probeᴸ = record { b = b₃ ; j = tw 1 ; β = β₁ ; x = zero ; c₀ = c₀ ; y = y₀ , e₀ ; w = wc ; on = refl }

fbᴸ : (c′ : Tr (tw 2)) → hdΩ (Fold.Probe.out probeᴸ c′) ≡ false
fbᴸ c′ = plus-ι _ _ (F.nz⊥ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (proj₂ (Rt-tw 3) c₀) (B₀ (h₃ c₀)) y₀)

offᴸ : Fold.Offᴾ foldᴸ probeᴸ
offᴸ c′ ne = fbᴸ c′

leg-wdec-tw3 : Fold.Hand foldᴸ (tw 3) → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
leg-wdec-tw3 H = leg-wdec H probeᴸ offᴸ

leg-not-hand : Fold.Hand foldᴸ (tw 3) → ⊥
leg-not-hand H = t≢f (trans (sym (trans (cong hdΩ (H b₃ (tw 1) c₀ (wc c₀) β₁ zero (y₀ , e₀))) (Fold.Probe.on probeᴸ)))
                            (fbᴸ c₀))

legI-not-J2Ωb : J2-Ωb legI → ⊥
legI-not-J2Ωb J = leg-not-hand (Frame.hand-Ω legI J (tw 2) h₃)
```
