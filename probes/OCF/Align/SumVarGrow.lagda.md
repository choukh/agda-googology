# 和形式, 层取可变位数 (四): 严格增长, 对一切位数一条定理

> 不含记号. 入口 [SumVar](SumVar.lagda.md). 序是布劳威尔树上的 `_≤_` ([TLRuleSpec](TLRuleSpec.lagda.md)). 工具 (L1 前缀与部分和, L2 节点非零, L3, L4 回灌第一格非零, `nz-κ`) 与 [SumClimbGrow](SumClimbGrow.lagda.md) 逐个对应, 只换层.
>
> 与三位时不同的是**站的定理不再按位数写**. 三位时 `SupN`, `SupR`, `Sup3` 是三条定理, 各自走一层 `P` 模块的前缀. 这里先把 "前缀之后的点" 做成数据 (`Pt`, `adv`), 再证:
>
> - `Inside i`: 深度 $i$ 的一段里的任何站都不超过这一段走完 (对 $i$ 归纳, 一条定理);
> - `Close`: 任何形如 `nl F ⨾ κN G ρ` 的闭包段, 在任何点上, 闭包站严格高于 `nl` 段的极限;
> - 合起来 `SupBlk`: **对一切深度 $i$, 一切高位, 一切点**, 闭包站严格高于段内任意可数族的上确界.
>
> 然后落到命名的站上: `SupSt` (秩内任一位置的闭包站), `SupD` (首位的闭包站), `SupTop` (秩 $j\to j+1$, 即 $\Omega^{j+1}$), `SuccSt` (最低位后继), `RankUp`, `T⁰≤Tω`, `Ts<Tω`, `Tω≤sup`. 都对一切秩, 一切位置.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumVarGrow where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumVarTree
open import OCF.Align.SumVarClosed
```

## §1 非零

```agda
data NZ₀ {Kd : A → Lay → Set} {V′ : ∀ {W L} → Kd W L → A → Set} {Z : Set} : ∀ {W} → D₊ Kd V′ Z W → Set where
  nz1 : ∀ {W} → NZ₀ (n1 {W = W})
  nzL : ∀ {W} {x y : D₊ Kd V′ Z W} → NZ₀ x → NZ₀ (x ⨾ y)
  nzR : ∀ {W} {x y : D₊ Kd V′ Z W} → NZ₀ y → NZ₀ (x ⨾ y)
  nzl : ∀ {W} {e : ℕ → D₊ Kd V′ Z W} → NZ₀ (e 0) → NZ₀ (nl e)
  nzw : ∀ {W₀ W} {p : W₀ ⊲ W} {x : D₊ Kd V′ Z W₀} → NZ₀ x → NZ₀ (nw p x)

sum≥ : ∀ {W} b (x : D₀ W) → b ≤ sum b x
sum≥ b x = ⊲→≤ (sum-fst b x)

nz≤ : ∀ {W} b {x : D₀ W} → NZ₀ x → asuc b ≤ sum b x
nz≤ b nz1 = ≤-refl _
nz≤ b {x ⨾ y} (nzL d) = ≤-trans (nz≤ b d) (sum≥ (sum b x) y)
nz≤ b {x ⨾ y} (nzR d) = ≤-trans (s≤ (sum≥ b x)) (nz≤ (sum b x) d)
nz≤ b (nzl d) = ≤l 1 (nz≤ b d)
nz≤ b (nzw {x = x′} d) = nz≤ b {x′} d

nz-drpZ : ∀ {L W W′} (z₀ : Zs L) {x : D₀ W} → NZ₀ x → NZ₀ (drpZ {W′ = W′} z₀ x)
nz-drpZ z₀ nz1 = nz1
nz-drpZ z₀ (nzL d) = nzL (nz-drpZ z₀ d)
nz-drpZ z₀ (nzR d) = nzR (nz-drpZ z₀ d)
nz-drpZ z₀ (nzl d) = nzl (nz-drpZ z₀ d)
nz-drpZ z₀ (nzw {x = x′} d) = nz-drpZ z₀ {x′} d

nzΩ : ∀ L {W} (l : AllLg L) → NZ₀ (Ωd L {W} l)
nzΩ [] _ = nz1
nzΩ (a ∷ L) _ = nzL nz1

nz-Step : ∀ {W} (Y : St W) {L m} (T′ : Tg W L m) → NZ₀ (yc (Step Y) T′)
nz-Step Y {L} T′ = nzl (nzL (nzΩ L _))

record Inv {W : A} (Y : St W) : Set where
  constructor iv
  field
    nzI : ∀ {L m} (T′ : Tg W L m) → NZ₀ (yc (d Y) T′)
open Inv public

record IZ {W : A} (Y : St W) : Set where
  constructor izz
  field
    nzZ : NZ₀ (z Y)
open IZ public

inv⊕ : ∀ {W} {Y : St W} (lW : Lg W) (Δ′ : Df W) → Inv Y → Inv (Y ⊕⟨ lW ⟩ Δ′)
inv⊕ lW Δ′ v = iv (λ T′ → nzL (nzI v T′))

iz⊕ : ∀ {W} {Y : St W} (lW : Lg W) (Δ′ : Df W) → IZ Y → IZ (Y ⊕⟨ lW ⟩ Δ′)
iz⊕ lW Δ′ v = izz (nzL (nzZ v))

invcv : ∀ {W W′} (q : W ⊲ W′) {Y : St W} → Inv Y → Inv (cv q Y)
invcv q v = iv (λ T′ → nzI v (tg↑ q T′))
```

## §2 不经过节点的路 (L3), 一个节点 (L2)

目标是空列表 (第 0 层); 节点不可能低于它, 所以总是上升.

```agda
record NZA {ly : Ly} {W : A} (A₀ : Ig ly W) (lW : Lg W) {m : A} (T′ : Tg W [] m) : Set where
  constructor na
  field
    nzA : ∀ (w : Dl ly W) (Y : St W) → NZ₀ (yc (A₀ C.self lW w Y) T′)
open NZA public

nz-Act : ∀ {ly W} (lW : Lg W) {m} (T′ : Tg W [] m) → NZA {ly} Act lW T′
nz-Act lW T′ = na (λ w Y → nz-Step Y T′)

L3 : ∀ {ly W₀ W} (ac : AccY ly) {x : Dl ly W₀} (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) {m} (T′ : Tg W [] m) →
     NZA A₀ lW T′ → NZ₀ x → ∀ w Y → NZ₀ (yc (Run ac x q₀ lW ll A₀ w Y) T′)
L3 ac q₀ lW ll A₀ T′ h nz1 w Y = nzA h w Y
L3 ac q₀ lW ll A₀ T′ h (nzL nx) w Y = nzL (L3 ac q₀ lW ll A₀ T′ h nx w Y)
L3 ac q₀ lW ll A₀ T′ h (nzR ny) w Y = nzR (L3 ac q₀ lW ll A₀ T′ h ny _ _)
L3 ac q₀ lW ll A₀ T′ h (nzl nd′) w Y = nzl (L3 ac q₀ lW ll A₀ T′ h nd′ w Y)
L3 ac q₀ lW ll A₀ T′ h (nzw {p = p} nx) w Y = L3 ac (⊲-tr p q₀) lW ll A₀ T′ h nx w Y

L2′ : ∀ {ly W₀ W L′ m} (ac : AccY ly) (ac′ : AccY (lay L′)) (x : K ly W₀ L′) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : Dl ly W) (Y : St W)
      (T′ : Tg W [] m) → NZA A₀ lW T′ → Inv Y → (o : Rk L′ [] m) → NZ₀ (RKi ac ac′ x (c1 x) q₀ lW ll A₀ w Y T′ o)
L2′ ac ac′ x q₀ lW ll A₀ w Y T′ hA v (keep (tz ()))
L2′ {ly} ac ac′ x q₀ lW ll A₀ w Y T′ hA v rise =
  nzl (L3 ac′ C.self lW (kk ly x q₀ ll) (Ai ac ac′ x (c1 x) q₀ (kk ly x q₀ ll) ll A₀ w) T′ (na (λ z′ Y′ → nzA hA _ Y′))
          (nzI v (tg C.self (kk ly x q₀ ll) lW)) n0 Y)

L2 : ∀ {ly W₀ W L′ m} (ac : AccY ly) (x : K ly W₀ L′) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : Dl ly W) (Y : St W)
     (T′ : Tg W [] m) → NZA A₀ lW T′ → Inv Y → NZ₀ (yc (Run ac (ni x (c1 x)) q₀ lW ll A₀ w Y) T′)
L2 {ly} (acc f) x q₀ lW ll A₀ w Y T′ hA v =
  L2′ (acc f) (f x) x q₀ lW ll A₀ w Y T′ hA v (rkT (hk↑ (kk ly x q₀ ll) (wm T′)) (dm T′) (lm T′))
```

## §3 前缀与部分和 (L1)

```agda
R : D̂ ω → D̂ ω → St ω → Df ω
R x w Y = Run accTop x C.self lω tt Act w Y

τ : Tg ω [] ω
τ = τ₀ lω

module P (F : ℕ → D̂ ω) (w : D̂ ω) (Y : St ω) where
  Rp : ℕ → D̂ ω × St ω
  Rp = Rpt accTop F C.self lω tt Act w Y

  dF : ℕ → D₀ ω
  dF j = yc (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) τ

  ptF : A → ℕ → ℕ → A
  ptF b k zero = b
  ptF b k (suc n) = ptF (sum b (dF k)) (suc k) n

  L1 : ∀ n k rest b → sum b (yc (R (Pfx F k n rest) (proj₁ (Rp k)) (proj₂ (Rp k))) τ) ≡ sum (ptF b k n) (yc (R rest (proj₁ (Rp (k + n))) (proj₂ (Rp (k + n)))) τ)
  L1 zero k rest b = cong (λ j → sum b (yc (R rest (proj₁ (Rp j)) (proj₂ (Rp j))) τ)) (sym (+-identityʳ k))
  L1 (suc n) k rest b =
    trans (L1 n (suc k) rest (sum b (dF k)))
          (cong (λ j → sum (ptF (sum b (dF k)) (suc k) n) (yc (R rest (proj₁ (Rp j)) (proj₂ (Rp j))) τ)) (sym (+-suc k n)))

  L1b : ∀ n k b → ptF b k (suc n) ≡ sum (ptF b k n) (dF (k + n))
  L1b zero k b = cong (λ j → sum b (dF j)) (sym (+-identityʳ k))
  L1b (suc n) k b = trans (L1b n (suc k) (sum b (dF k))) (cong (λ j → sum (ptF (sum b (dF k)) (suc k) n) (dF j)) (sym (+-suc k n)))

  ptF≡pt : ∀ n b → ptF b 0 n ≡ pt b dF n
  ptF≡pt zero b = refl
  ptF≡pt (suc n) b = trans (L1b n 0 b) (cong (λ x → sum x (dF n)) (ptF≡pt n b))

  inv-Rp : Inv Y → ∀ j → Inv (proj₂ (Rp j))
  inv-Rp v zero = v
  inv-Rp v (suc j) = inv⊕ lω (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) (inv-Rp v j)

  iz-Rp : IZ Y → ∀ j → IZ (proj₂ (Rp j))
  iz-Rp v zero = v
  iz-Rp v (suc j) = iz⊕ lω (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) (iz-Rp v j)

≡≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
≡≤ refl q = q

≤≡ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤≡ q refl = q

≡→≤ : ∀ {a b} → a ≡ b → a ≤ b
≡→≤ refl = ≤-refl _

alim≤ : ∀ {f g : ℕ → A} → (∀ k → f k ≤ g k) → alim f ≤ alim g
alim≤ h = l≤ (λ k → ≤l k (h k))
```

## §4 回灌的第一格 (L4)

对任何闭包 `κN G ρ` (节点的层由 `ρ` 给, 位数任意), 对任何满足 `Inv`, `IZ` 的状态, 它在目标 `[]` 上的输出非零. 同 `SumClimbGrow`.

```agda
module W (G′ : A → Lay) (ρ : ∀ {c} → ω ⊲ c → AllB (G′ c) c) (V₁ : A) (lV : Lg V₁) (A₀ : Ig top V₁) (hA : NZA A₀ lV (τ₀ lV)) where
  u² : ∀ {c} → ω ⊲ c → Lg c → D̂ c
  u² p _ = ni (ρ p) (c1 (ρ p))

  NZW : ∀ b {a} → a ⊲ b → ω ⊲ a → Lg b → Set
  NZW b P ap lb = ∀ (bV : b ⊲ V₁) co (Y : St V₁) → Inv Y → NZ₀ (yc (Walk accTop u² b P ap lb bV lV tt A₀ co Y) (τ₀ lV))

  W-suc : ∀ c {a} (P : a ⊲ c) ap lb → NZW (asuc c) (C.suc P) ap lb
  W-suc c P ap lb bV co Y v =
    nzR (L2 accTop (ρ (⊲-tr ap P)) (⊲-tr (C.suc C.self) bV) lV tt A₀ (co ⨾ Cut u² c P ap lb (⊲-tr (C.suc C.self) bV))
           (Y ⊕⟨ lV ⟩ Walk accTop u² c P ap lb (⊲-tr (C.suc C.self) bV) lV tt A₀ co Y) (τ₀ lV) hA
           (inv⊕ lV (Walk accTop u² c P ap lb (⊲-tr (C.suc C.self) bV) lV tt A₀ co Y) v))

  W-ext : ∀ {W₀′} b″ {a} (P : a ⊲ b″) ap lb″ (y : D₀ W₀′) → NZW b″ P ap lb″ → NZW (sum b″ y) (⊲-tr P (sum-fst b″ y)) ap (Lg-sum b″ y lb″)
  W-ext b″ P ap lb″ n0 h = h
  W-ext b″ P ap lb″ n1 h = W-suc b″ P ap lb″
  W-ext b″ P ap lb″ (y₁ ⨾ y₂) h =
    subst (λ π → NZW (sum (sum b″ y₁) y₂) π ap (Lg-sum (sum b″ y₁) y₂ (Lg-sum b″ y₁ lb″)))
          (sym (⊲-as P (sum-fst b″ y₁) (sum-fst (sum b″ y₁) y₂)))
          (W-ext (sum b″ y₁) (⊲-tr P (sum-fst b″ y₁)) ap (Lg-sum b″ y₁ lb″) y₂ (W-ext b″ P ap lb″ y₁ h))
  W-ext b″ P ap lb″ (nl e) h bV co Y v = nzL (h _ co Y v)
  W-ext b″ P ap lb″ (ni (tz ()) u) h
  W-ext b″ P ap lb″ (nκ () u) h
  W-ext b″ P ap lb″ (nw p y) h = W-ext b″ P ap lb″ y h

  L4 : ∀ {W₀′} (z′ : D₀ W₀′) → NZ₀ z′ → ∀ b′ {a} (Rr : a ⊲ b′) ap lb′ → NZW (sum b′ z′) (⊲-tr Rr (sum-fst b′ z′)) ap (Lg-sum b′ z′ lb′)
  L4 n1 nz1 b′ Rr ap lb′ = W-suc b′ Rr ap lb′
  L4 (x ⨾ y) (nzL nx) b′ Rr ap lb′ =
    subst (λ π → NZW (sum (sum b′ x) y) π ap (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)))
          (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
          (W-ext (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) ap (Lg-sum b′ x lb′) y (L4 x nx b′ Rr ap lb′))
  L4 (x ⨾ y) (nzR ny) b′ Rr ap lb′ =
    subst (λ π → NZW (sum (sum b′ x) y) π ap (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)))
          (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
          (L4 y ny (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) ap (Lg-sum b′ x lb′))
  L4 (nl e) (nzl ne) b′ Rr ap lb′ bV co Y v =
    nzR (nzl (subst (λ π → NZW (sum b′ (e 0)) π (⊲-tr ap Rr) (Lg-sum b′ (e 0) lb′)) (⊲-idl (sum-fst b′ (e 0)))
                    (L4 (e 0) ne b′ C.self (⊲-tr ap Rr) lb′) (⊲-tr (C.lim 1 C.self) bV) (co ⨾ Cut u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV))
                    (Y ⊕⟨ lV ⟩ Walk accTop u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV tt A₀ co Y)
                    (inv⊕ lV (Walk accTop u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV tt A₀ co Y) v)))
  L4 (nw p x) (nzw nx) b′ Rr ap lb′ = L4 x nx b′ Rr ap lb′

-- 闭包在任何满足 Inv, IZ 的状态上非零; 对一切位数的节点层
nz-κ : ∀ (G′ : A → Lay) (ρ : ∀ {c} → ω ⊲ c → AllB (G′ c) c) (w : D̂ ω) (Y : St ω) → Inv Y → IZ Y → NZ₀ (yc (R (κN G′ ρ) w Y) τ)
nz-κ G′ ρ w Y v iz =
  nzl (nz-drpZ z[] (W.L4 G′ ρ (sum ω (z Y)) (Lg-sum ω (z Y) lω) (Ig↾ (sum-fst ω (z Y)) Act) (nz-Act (Lg-sum ω (z Y) lω) (τ₀ (Lg-sum ω (z Y) lω)))
                    (z Y) (nzZ iz) ω C.self C.self lω C.self (nw (sum-fst ω (z Y)) w) (cv (sum-fst ω (z Y)) Y) (invcv (sum-fst ω (z Y)) v)))
```

## §5 点: 前缀走完之后

`Pt`: 坐标, 状态, 到此为止的第 0 层的和, 以及状态的两条不变式. `Val p x`: 从点 `p` 接着走输入 `x` 之后的和. `adv p F n`: 走完 `F 0 ⨾ … ⨾ F (n-1)` 之后的点.

```agda
record Pt : Set where
  constructor mkP
  field
    pw : D̂ ω
    pY : St ω
    pb : A
    pv : Inv pY
    pz : IZ pY
open Pt public

Val : Pt → D̂ ω → A
Val p x = sum (pb p) (yc (R x (pw p) (pY p)) τ)

adv : Pt → (ℕ → D̂ ω) → ℕ → Pt
adv p F n = mkP (proj₁ (P.Rp F (pw p) (pY p) n)) (proj₂ (P.Rp F (pw p) (pY p) n)) (P.ptF F (pw p) (pY p) (pb p) 0 n)
                (P.inv-Rp F (pw p) (pY p) (pv p) n) (P.iz-Rp F (pw p) (pY p) (pz p) n)

seqP : Pt → D̂ ω → Pt
seqP p x = mkP (pw p ⨾ nw C.self x) (pY p ⊕⟨ lω ⟩ R x (pw p) (pY p)) (Val p x) (inv⊕ lω _ (pv p)) (iz⊕ lω _ (pz p))

-- 前缀
L1′ : ∀ p F n rest → Val p (Pfx F 0 n rest) ≡ Val (adv p F n) rest
L1′ p F n rest = P.L1 F (pw p) (pY p) n 0 rest (pb p)

-- 走完第 n 段就是第 n+1 个点
Next : ∀ p F n → Val (adv p F n) (F n) ≡ Val (adv p F (suc n)) n0
Next p F n = sym (P.L1b F (pw p) (pY p) n 0 (pb p))

-- 第 n 段走完不超过 nl 的极限
InF : ∀ p F n → Val (adv p F n) (F n) ≤ Val p (nl F)
InF p F n = ≡≤ (trans (Next p F n) (P.ptF≡pt F (pw p) (pY p) (suc n) (pb p))) (⊲→≤ (C.lim (suc n) C.self))

Seq≤ : ∀ p x y → Val p x ≤ Val p (x ⨾ y)
Seq≤ p x y = sum≥ (Val p x) _

nil≤ : ∀ p x → Val p n0 ≤ Val p x
nil≤ p x = sum≥ (pb p) _
```

## §6 对一切深度的三条定理

**`Succ`.** 一个节点在任何点上非零.

```agda
Succ : ∀ p ns → asuc (Val p n0) ≤ Val p (nd ns)
Succ p ns = nz≤ (pb p) (L2 accTop (allN ns) C.self lω tt Act (pw p) (pY p) τ (nz-Act lω τ) (pv p))
```

**`Close`.** 任何闭包段 `nl F ⨾ κN G ρ`, 在任何点上: 闭包站严格高于 `nl` 段的极限.

```agda
Close : ∀ p F (G′ : A → Lay) (ρ : ∀ {c} → ω ⊲ c → AllB (G′ c) c) → asuc (Val p (nl F)) ≤ Val p (nl F ⨾ κN G′ ρ)
Close p F G′ ρ = nz≤ (Val p (nl F)) (nz-κ G′ ρ (pw (seqP p (nl F))) (pY (seqP p (nl F))) (pv (seqP p (nl F))) (pz (seqP p (nl F))))
```

**`Inside`.** 深度 $i$ 的一段 `Blk i ns` 里, 由各位 `es` 给的任何站, 都不超过这一段走完; 对 $i$ 归纳, 对一切高位 `ns`, 一切点.

```agda
InsideL : ∀ i ns e (es : Vec ℕ i) p → Val p (Pr ns (e ∷ es) n0) ≤ Val p (nl (λ c → Blk i (c ∷ ns)))
Inside  : ∀ i ns (es : Vec ℕ i) p → Val p (Pr ns es n0) ≤ Val p (Blk i ns)
InsideL i ns e es p =
  ≡≤ (L1′ p (λ c → Blk i (c ∷ ns)) e (Pr (e ∷ ns) es n0))
     (≤-trans (Inside i (e ∷ ns) es (adv p (λ c → Blk i (c ∷ ns)) e)) (InF p (λ c → Blk i (c ∷ ns)) e))
Inside zero ns [] p = nil≤ p (nd ns)
Inside (suc i) ns (e ∷ es) p = ≤-trans (InsideL i ns e es p) (Seq≤ p (nl (λ c → Blk i (c ∷ ns))) (κ i ns))
```

**`SupF`, `SupBlk`.** 闭包站严格高于段内任意可数族的上确界. `SupBlk` 对一切深度 $i$, 一切高位, 一切点, 一条定理; 三位时的 `SupN`, `SupR`, `Sup3` 是它的三个实例.

```agda
SupF : ∀ p (F : ℕ → D̂ ω) (G′ : A → Lay) (ρ : ∀ {c} → ω ⊲ c → AllB (G′ c) c) (g : ℕ → ℕ) (x : ℕ → D̂ ω) →
       (∀ k → Val (adv p F (g k)) (x k) ≤ Val (adv p F (g k)) (F (g k))) →
       asuc (alim (λ k → Val p (Pfx F 0 (g k) (x k)))) ≤ Val p (nl F ⨾ κN G′ ρ)
SupF p F G′ ρ g x h = ≤-trans (s≤ (l≤ (λ k → ≡≤ (L1′ p F (g k) (x k)) (≤-trans (h k) (InF p F (g k)))))) (Close p F G′ ρ)

SupBlk : ∀ i ns p (g : ℕ → ℕ × Vec ℕ i) → asuc (alim (λ k → Val p (Pr ns (proj₁ (g k) ∷ proj₂ (g k)) n0))) ≤ Val p (Blk (suc i) ns)
SupBlk i ns p g =
  SupF p (λ c → Blk i (c ∷ ns)) (λ c → zs i (c ∷ lyN ns)) (ρκ i ns) (λ k → proj₁ (g k)) (λ k → Pr (proj₁ (g k) ∷ ns) (proj₂ (g k)) n0)
       (λ k → Inside i (proj₁ (g k) ∷ ns) (proj₂ (g k)) (adv p (λ c → Blk i (c ∷ ns)) (proj₁ (g k))))
```

## §7 落到命名的站

`p₁`: 走完 `1 ⨾ nd []` 的点. `pR j`: 再走完 `Rj 0 ⨾ … ⨾ Rj (j-1)`. `pD j d`: 再走完 `Blk j [1] ⨾ … ⨾ Blk j [d]`. 站的高位前缀 `pre` 走完的点是 `ptS`.

```agda
p₀ : Pt
p₀ = mkP (n0 ⨾ nw C.self n1) (Y₀ ⊕⟨ lω ⟩ Step (Y₀ {ω})) (sum (sum {ω} azero n1) (yc (Step (Y₀ {ω})) τ))
         (iv (λ T′ → nzR (nz-Step (Y₀ {ω}) T′))) (izz (nzR (nz-Step (Y₀ {ω}) τ)))

p₁ : Pt
p₁ = seqP p₀ (nd [])

Fj : ℕ → ℕ → D̂ ω
Fj j n = Blk j (suc n ∷ [])

pR : ℕ → Pt
pR j = adv p₁ Rj j

pD : ℕ → ℕ → Pt
pD j d = adv (pR j) (Fj j) d

zeros : ∀ i → Vec ℕ i
zeros zero = []
zeros (suc i) = 0 ∷ zeros i

PrZ : ∀ {i} ns rest → Pr ns (zeros i) rest ≡ rest
PrZ {i = zero} ns rest = refl
PrZ {suc i} ns rest = PrZ {i} (0 ∷ ns) rest

rv : ∀ {a} → List ℕ → Vec ℕ a → List ℕ
rv ns [] = ns
rv ns (e ∷ es) = rv (e ∷ ns) es

ptS : Pt → List ℕ → ∀ {a} → Vec ℕ a → ℕ → Pt
ptS p ns [] m = p
ptS p ns {suc a} (e ∷ es) m = ptS (adv p (λ c → Blk (a + m) (c ∷ ns)) e) (e ∷ ns) es m

PrApp : ∀ {a m} p ns (pre : Vec ℕ a) (rest : Vec ℕ m) r → Val p (Pr ns (pre ++ rest) r) ≡ Val (ptS p ns pre m) (Pr (rv ns pre) rest r)
PrApp p ns [] rest r = refl
PrApp {suc a} {m} p ns (e ∷ es) rest r =
  trans (L1′ p (λ c → Blk (a + m) (c ∷ ns)) e (Pr (e ∷ ns) (es ++ rest) r)) (PrApp (adv p (λ c → Blk (a + m) (c ∷ ns)) e) (e ∷ ns) es rest r)

T⁰V : ∀ j → T⁰ j ≡ pb (pR j)
T⁰V j = L1′ p₁ Rj j n0

TsV : ∀ j d ds → Ts j d ds ≡ Val (pD j d) (Pr (suc d ∷ []) ds n0)
TsV j d ds = trans (L1′ p₁ Rj j _) (L1′ (pR j) (Fj j) d _)
```

**`SuccSt`.** 最低位后继: 对一切秩, 一切前缀.

```agda
SuccSt : ∀ a d (pre : Vec ℕ a) e → asuc (Ts (a + 1) d (pre ++ (e ∷ []))) ≤ Ts (a + 1) d (pre ++ (suc e ∷ []))
SuccSt a d pre e =
  ≡≤ (cong asuc (trans (TsV (a + 1) d (pre ++ (e ∷ []))) (trans (PrApp (pD (a + 1) d) (suc d ∷ []) pre (e ∷ []) n0) (L1′ q F e n0))))
     (≤≡ (Succ (adv q F e) (e ∷ L))
         (sym (trans (TsV (a + 1) d (pre ++ (suc e ∷ []))) (trans (PrApp (pD (a + 1) d) (suc d ∷ []) pre (suc e ∷ []) n0)
                (trans (L1′ q F (suc e) n0) (sym (Next q F e)))))))
  where
  q = ptS (pD (a + 1) d) (suc d ∷ []) pre 1
  L = rv (suc d ∷ []) pre
  F = λ c → Blk 0 (c ∷ L)
```

**`SupSt`.** 秩内任一位置的闭包站: 前缀 `pre`, 这一位 `e`, 其下 $i+1$ 位走遍任意可数族; 闭包站是 `e+1` 之后补零.

```agda
SupSt : ∀ a i d (pre : Vec ℕ a) e (g : ℕ → ℕ × Vec ℕ i) →
        asuc (alim (λ k → Ts (a + suc (suc i)) d (pre ++ (e ∷ proj₁ (g k) ∷ proj₂ (g k))))) ≤ Ts (a + suc (suc i)) d (pre ++ (suc e ∷ zeros (suc i)))
SupSt a i d pre e g =
  ≤-trans (s≤ (alim≤ (λ k → ≡→≤ (trans (TsV j d (pre ++ (e ∷ proj₁ (g k) ∷ proj₂ (g k))))
                                   (trans (PrApp (pD j d) (suc d ∷ []) pre (e ∷ proj₁ (g k) ∷ proj₂ (g k)) n0)
                                          (L1′ q F e (Pr (e ∷ L) (proj₁ (g k) ∷ proj₂ (g k)) n0)))))))
          (≤≡ (SupBlk i (e ∷ L) (adv q F e) g)
              (sym (trans (TsV j d (pre ++ (suc e ∷ zeros (suc i))))
                     (trans (PrApp (pD j d) (suc d ∷ []) pre (suc e ∷ zeros (suc i)) n0)
                       (trans (L1′ q F (suc e) (Pr (suc e ∷ L) (zeros (suc i)) n0))
                         (trans (cong (Val (adv q F (suc e))) (PrZ (suc e ∷ L) n0)) (sym (Next q F e))))))))
  where
  j = a + suc (suc i)
  q = ptS (pD j d) (suc d ∷ []) pre (suc (suc i))
  L = rv (suc d ∷ []) pre
  F = λ c → Blk (suc i) (c ∷ L)
```

**`SupD`.** 首位的闭包站: 秩 $i+1$ 里首位 $d$ 之下一切站的任意可数族, 严格低于首位 $d+1$ 的第一站.

```agda
SupD : ∀ i d (g : ℕ → ℕ × Vec ℕ i) → asuc (alim (λ k → Ts (suc i) d (proj₁ (g k) ∷ proj₂ (g k)))) ≤ Ts (suc i) (suc d) (zeros (suc i))
SupD i d g =
  ≤-trans (s≤ (alim≤ (λ k → ≡→≤ (TsV (suc i) d (proj₁ (g k) ∷ proj₂ (g k))))))
          (≤≡ (SupBlk i (suc d ∷ []) (pD (suc i) d) g)
              (sym (trans (TsV (suc i) (suc d) (zeros (suc i)))
                     (trans (cong (Val (pD (suc i) (suc d))) (PrZ (suc (suc d) ∷ []) n0)) (sym (Next (pR (suc i)) (Fj (suc i)) d))))))
```

**`SupTop`.** 秩 $j\to j+1$: 首位在第 $j$ 位的一切站 (读法 $\Omega^j\cdot(d+1)+\dots$) 的任意可数族, 严格低于 $\Omega^{j+1}$ 的站 `T⁰ (suc j)`.

```agda
SupTop : ∀ j (g : ℕ → ℕ × Vec ℕ j) → asuc (alim (λ k → Ts j (proj₁ (g k)) (proj₂ (g k)))) ≤ T⁰ (suc j)
SupTop j g =
  ≤-trans (s≤ (alim≤ (λ k → ≡→≤ (L1′ p₁ Rj j _))))
          (≤≡ (SupF (pR j) (Fj j) (λ c → zs j (c ∷ [])) (ρκ j []) (λ k → proj₁ (g k)) (λ k → Pr (suc (proj₁ (g k)) ∷ []) (proj₂ (g k)) n0)
                    (λ k → Inside j (suc (proj₁ (g k)) ∷ []) (proj₂ (g k)) (adv (pR j) (Fj j) (proj₁ (g k)))))
              (sym (trans (T⁰V (suc j)) (sym (Next p₁ Rj j)))))
```

**秩与 $\Omega^\omega$.**

```agda
RankUp : ∀ j → asuc (T⁰ j) ≤ T⁰ (suc j)
RankUp j =
  ≡≤ (cong asuc (T⁰V j))
     (≤-trans (s≤ (nil≤ (pR j) (nl (Fj j)))) (≤≡ (Close (pR j) (Fj j) (λ c → zs j (c ∷ [])) (ρκ j [])) (sym (trans (T⁰V (suc j)) (sym (Next p₁ Rj j))))))

T⁰≤Tω : ∀ j → T⁰ j ≤ Tω
T⁰≤Tω j = ≡≤ (trans (T⁰V j) (P.ptF≡pt Rj (pw p₁) (pY p₁) j (pb p₁))) (⊲→≤ (C.lim j C.self))

-- Ω^ω 恰是各秩的极限: 不多出什么
Tω≤sup : Tω ≤ alim T⁰
Tω≤sup = alim≤ (λ j → ≡→≤ (sym (trans (T⁰V j) (P.ptF≡pt Rj (pw p₁) (pY p₁) j (pb p₁)))))

sup≤Tω : alim T⁰ ≤ Tω
sup≤Tω = l≤ T⁰≤Tω

Ts≤T⁰ : ∀ j d ds → asuc (Ts j d ds) ≤ T⁰ (suc j)
Ts≤T⁰ j d ds = ≤-trans (s≤ (≤l 0 (≤-refl _))) (SupTop j (λ _ → d , ds))

Ts<Tω : ∀ j d ds → asuc (Ts j d ds) ≤ Tω
Ts<Tω j d ds = ≤-trans (Ts≤T⁰ j d ds) (T⁰≤Tω (suc j))

T⁰<Tω : ∀ j → asuc (T⁰ j) ≤ Tω
T⁰<Tω j = ≤-trans (RankUp j) (T⁰≤Tω (suc j))
```

## §8 几个具体的站

```agda
-- Ω² 站的两种写法是同一个点
Ω²≡ : T⁰ 2 ≡ Ts 2 0 (zeros 2)
Ω²≡ = trans (T⁰V 2) (sym (TsV 2 0 (zeros 2)))

Ω²<Ω²+1 : asuc (Ts 2 0 (0 ∷ 0 ∷ [])) ≤ TΩ²+1
Ω²<Ω²+1 = SuccSt 1 0 (0 ∷ []) 0

Ω²+1<Ω²·2 : asuc TΩ²+1 ≤ TΩ²·2
Ω²+1<Ω²·2 = ≤-trans (s≤ (≤l 0 (≤-refl _))) (SupD 1 0 (λ _ → 0 , (1 ∷ [])))

Ω³<Ω⁴ : asuc TΩ³ ≤ TΩ⁴
Ω³<Ω⁴ = RankUp 3

Ω⁴<Ω^ω : asuc TΩ⁴ ≤ TΩ^ω
Ω⁴<Ω^ω = T⁰<Tω 4
```
