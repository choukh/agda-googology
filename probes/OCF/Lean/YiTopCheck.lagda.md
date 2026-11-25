# 顶槽位的块: J2 与对空白页的对应

> 验收文件. 编译定理, 无前提: J2 的对应物 (`J2-suc`, `J2-lim`, `J2⊥`); 与空白页的块的对应 `Lr` (层号), `Rel` (树) 对两种折叠都保持 (`rel⊥`, `rels`), 塔, Λ, Ω 树, 读法 ψ₀(Λ) 的闭项相对应 (`tw-rel`, `Λ-rel`, `Ωt-rel`, `EBO-rel`).
> `Rel` 只把顶槽位结点对到空白页的顶槽位结点; 第 0 层上它是逐点相同 (布劳威尔树的互模拟). 对应是关系不是函数: `Ωₗ` 的分支定义域在层号里是逆变的, 函数嵌入要反方向的投影, 且证投影是左逆要函数外延 (判断, 没有编译).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTopCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiTopBlock
open import OCF.Lean.YiTopFold
open import OCF.Lean.YiTopLegal using (dS; dL; dW; seq; EBOᶜ)
import OCF.Lean.YiFreshBlock as F
import OCF.Lean.YiFreshFold as G
import OCF.Lean.YiFreshLegal as GL
```

## 1 J2: 嵌入分支里的折叠等于孩子层里的折叠

```agda
J2-suc : (a : L) (B : Base (suc a)) (j : L) (w : j ≤ a) (x : Tr (suc a)) (y : Tr a)
  → ψs (suc a) B j (ins w) (up x tt y)
  ≡ ψs a (base (ψ⊥ (suc a) B x) (λ j′ w′ → ψs (suc a) B j′ (ins w′) x)) j w y
J2-suc a B j w x y = refl

J2-lim : (g : ℕ → L) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
         (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) B j (inl n w) (up x n y)
  ≡ ψs (g n) (base (ψ⊥ (lim g) B x) (λ j′ w′ → ψs (lim g) B j′ (inl n w′) x)) j w y
J2-lim g B n j w x y rewrite eqℕ-refl n = refl

J2⊥ : (ℓ : L) (B : Base ℓ) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c)
  → Σ (Base (chL ℓ c)) λ B′ → (b⊥ B′ ≡ ψ⊥ ℓ B x) × (ψ⊥ ℓ B (up x c y) ≡ ψ⊥ (chL ℓ c) B′ (chT ℓ c y))
J2⊥ (suc a)  B x c y = _ , refl , refl
J2⊥ (lim g)  B x n y = _ , refl , refl
J2⊥ (Ωₗ k h) B x c y = _ , refl , refl
```

## 2 对应

对本块的树递归, 空白页一侧用等式给出头构造子; Ω 结点只对到空白页的顶槽位 (后继层号的 `inj₁ tt`, `Ωₗ` 层号的 `inj₁ (inj₁ tt)`).

```agda
mutual
  Lr : L → F.L → Set
  Lr zero     ℓ′ = ℓ′ ≡ F.zero
  Lr (suc a)  ℓ′ = Σ F.L λ a′ → (ℓ′ ≡ F.suc a′) × Lr a a′
  Lr (lim g)  ℓ′ = Σ (ℕ → F.L) λ g′ → (ℓ′ ≡ F.lim g′) × ((n : ℕ) → Lr (g n) (g′ n))
  Lr (Ωₗ k h) ℓ′ = Σ F.L λ k′ → Σ (F.Tr k′ → F.L) λ h′ → (ℓ′ ≡ F.Ωₗ k′ h′)
                 × Σ (Lr k k′) λ r → (c : Tr k) (c′ : F.Tr k′) → Rel k k′ r c c′ → Lr (h c) (h′ c′)

  Rel : (ℓ : L) (ℓ′ : F.L) → Lr ℓ ℓ′ → Tr ℓ → F.Tr ℓ′ → Set
  Rel ℓ ℓ′ r zero    x′ = x′ ≡ F.zero
  Rel ℓ ℓ′ r (suc x) x′ = Σ (F.Tr ℓ′) λ y′ → (x′ ≡ F.suc y′) × Rel ℓ ℓ′ r x y′
  Rel ℓ ℓ′ r (lim f) x′ = Σ (ℕ → F.Tr ℓ′) λ f′ → (x′ ≡ F.lim f′) × ((n : ℕ) → Rel ℓ ℓ′ r (f n) (f′ n))
  Rel (suc a) .(F.suc a′) (a′ , refl , r) (Ω _ g) x′ =
    Σ (F.Tr a′ → F.Tr (F.suc a′)) λ g′ → (x′ ≡ F.Ω (inj₁ tt) g′)
    × ((z : Tr a) (z′ : F.Tr a′) → Rel a a′ r z z′ → Rel (suc a) (F.suc a′) (a′ , refl , r) (g z) (g′ z′))
  Rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (Ω _ g) x′ =
    Σ (F.Tr k′ → F.Tr (F.Ωₗ k′ h′)) λ g′ → (x′ ≡ F.Ω (inj₁ (inj₁ tt)) g′)
    × ((z : Tr k) (z′ : F.Tr k′) → Rel k k′ r z z′
       → Rel (Ωₗ k h) (F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (g z) (g′ z′))
  Rel zero    _ _ (Ω () _) _
  Rel (lim _) _ _ (Ω () _) _
  Rel (suc a) .(F.suc a′) (a′ , refl , r) (up x _ y) x′ =
    Σ (F.Tr (F.suc a′)) λ x″ → Σ (F.Tr a′) λ y′ → (x′ ≡ F.up x″ tt y′)
    × Rel (suc a) (F.suc a′) (a′ , refl , r) x x″ × Rel a a′ r y y′
  Rel (lim g) .(F.lim g′) (g′ , refl , r) (up x n y) x′ =
    Σ (F.Tr (F.lim g′)) λ x″ → Σ (F.Tr (g′ n)) λ y′ → (x′ ≡ F.up x″ n y′)
    × Rel (lim g) (F.lim g′) (g′ , refl , r) x x″ × Rel (g n) (g′ n) (r n) y y′
  Rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (up x c y) x′ =
    Σ (F.Tr (F.Ωₗ k′ h′)) λ x″ → Σ (F.Tr k′) λ c′ → Σ (Rel k k′ r c c′) λ rc → Σ (F.Tr (h′ c′)) λ y′
    → (x′ ≡ F.up x″ c′ y′)
    × Rel (Ωₗ k h) (F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) x x″ × Rel (h c) (h′ c′) (rh c c′ rc) y y′
  Rel zero _ _ (up _ () _) _
```

目标路径的对应, 连同目标层号的对应 (最后一个下标).

```agda
data Wr : {ℓ : L} {ℓ′ : F.L} {j : L} {j′ : F.L} → Lr ℓ ℓ′ → j ≤ ℓ → j′ G.≤ ℓ′ → Lr j j′ → Set where
  wself : ∀ {ℓ ℓ′} {r : Lr ℓ ℓ′} → Wr r self G.self r
  wins  : ∀ {a a′ j j′} {r : Lr a a′} {w : j ≤ a} {w′ : j′ G.≤ a′} {q} → Wr r w w′ q
        → Wr {suc a} {F.suc a′} (a′ , refl , r) (ins w) (G.ins w′) q
  winl  : ∀ {g g′ j j′} {r : (n : ℕ) → Lr (g n) (g′ n)} {n} {w : j ≤ g n} {w′ : j′ G.≤ g′ n} {q}
        → Wr (r n) w w′ q → Wr {lim g} {F.lim g′} (g′ , refl , r) (inl n w) (G.inl n w′) q
  wink  : ∀ {k h k′ h′ j j′} {r : Lr k k′} {rh} {w : j ≤ k} {w′ : j′ G.≤ k′} {q}
        → Wr r w w′ q → Wr {Ωₗ k h} {F.Ωₗ k′ h′} (k′ , h′ , refl , r , rh) (ink w) (G.ink w′) q
  winb  : ∀ {k h k′ h′ j j′} {r : Lr k k′} {rh} {c c′} (rc : Rel k k′ r c c′)
          {w : j ≤ h c} {w′ : j′ G.≤ h′ c′} {q}
        → Wr (rh c c′ rc) w w′ q → Wr {Ωₗ k h} {F.Ωₗ k′ h′} (k′ , h′ , refl , r , rh) (inb c w) (G.inb c′ w′) q

RelB : (ℓ : L) (ℓ′ : F.L) → Lr ℓ ℓ′ → Base ℓ → G.Base ℓ′ → Set
RelB ℓ ℓ′ r B B′ = Rel zero F.zero refl (b⊥ B) (G.b⊥ B′)
  × (∀ {j j′} {w : j ≤ ℓ} {w′ : j′ G.≤ ℓ′} {q} → Wr r w w′ q → Rel j j′ q (bs B j w) (G.bs B′ j′ w′))
```

## 3 运算保持对应

```agda
+-rel : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) {a : Tr ℓ} {a′ : F.Tr ℓ′} (b : Tr ℓ) (b′ : F.Tr ℓ′)
      → Rel ℓ ℓ′ r a a′ → Rel ℓ ℓ′ r b b′ → Rel ℓ ℓ′ r (a + b) (a′ G.+ b′)
+-rel ℓ ℓ′ r zero    .F.zero      ra refl = ra
+-rel ℓ ℓ′ r (suc b) .(F.suc y′) ra (y′ , refl , rb) = _ , refl , +-rel ℓ ℓ′ r b y′ ra rb
+-rel ℓ ℓ′ r (lim f) .(F.lim f′) ra (f′ , refl , rf) = _ , refl , λ n → +-rel ℓ ℓ′ r (f n) (f′ n) ra (rf n)
+-rel (suc a) .(F.suc a′) (a′ , refl , r) (Ω _ g) .(F.Ω (inj₁ tt) g′) ra (g′ , refl , rg) =
  _ , refl , λ z z′ rz → +-rel (suc a) (F.suc a′) (a′ , refl , r) (g z) (g′ z′) ra (rg z z′ rz)
+-rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (Ω _ g) .(F.Ω (inj₁ (inj₁ tt)) g′) ra (g′ , refl , rg) =
  _ , refl , λ z z′ rz → +-rel (Ωₗ k h) (F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (g z) (g′ z′) ra (rg z z′ rz)
+-rel zero    _ _ (Ω () _) _ _ _
+-rel (lim _) _ _ (Ω () _) _ _ _
+-rel (suc a) .(F.suc a′) (a′ , refl , r) (up y _ w) .(F.up y′ tt w′) ra (y′ , w′ , refl , ry , rw) =
  _ , _ , refl , +-rel (suc a) (F.suc a′) (a′ , refl , r) y y′ ra ry , rw
+-rel (lim g) .(F.lim g′) (g′ , refl , r) (up y n w) .(F.up y′ n w′) ra (y′ , w′ , refl , ry , rw) =
  _ , _ , refl , +-rel (lim g) (F.lim g′) (g′ , refl , r) y y′ ra ry , rw
+-rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (up y c w) .(F.up y′ c′ w′) ra
      (y′ , c′ , rc , w′ , refl , ry , rw) =
  _ , _ , rc , _ , refl , +-rel (Ωₗ k h) (F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) y y′ ra ry , rw
+-rel zero _ _ (up _ () _) _ _ _

ι-rel : (j : L) (j′ : F.L) (q : Lr j j′) (a : Tr zero) (a′ : F.Tr F.zero)
      → Rel zero F.zero refl a a′ → Rel j j′ q (ι j a) (G.ι j′ a′)
ι-rel j j′ q zero    .F.zero      refl = refl
ι-rel j j′ q (suc a) .(F.suc a′) (a′ , refl , ra) = _ , refl , ι-rel j j′ q a a′ ra
ι-rel j j′ q (lim f) .(F.lim f′) (f′ , refl , rf) = _ , refl , λ n → ι-rel j j′ q (f n) (f′ n) (rf n)
ι-rel j j′ q (Ω () _) _ _
ι-rel j j′ q (up _ () _) _ _

next-rel : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) (b : Tr ℓ) (b′ : F.Tr ℓ′)
         → Rel ℓ ℓ′ r b b′ → Rel ℓ ℓ′ r (next b) (G.next b′)
next-rel ℓ ℓ′ r b b′ rb = _ , refl , go
  where
  go : (n : ℕ) → Rel ℓ ℓ′ r (iter (b +_) b n) (G.iter (b′ G.+_) b′ n)
  go zero    = rb
  go (suc n) = +-rel ℓ ℓ′ r _ _ rb (go n)

cum-rel : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) (Φ : ℕ → Tr ℓ) (Φ′ : ℕ → F.Tr ℓ′)
        → ((n : ℕ) → Rel ℓ ℓ′ r (Φ n) (Φ′ n)) → (n : ℕ) → Rel ℓ ℓ′ r (cum Φ n) (G.cum Φ′ n)
cum-rel ℓ ℓ′ r Φ Φ′ hΦ zero    = hΦ zero
cum-rel ℓ ℓ′ r Φ Φ′ hΦ (suc n) = +-rel ℓ ℓ′ r (Φ (suc n)) (Φ′ (suc n)) (cum-rel ℓ ℓ′ r Φ Φ′ hΦ n) (hΦ (suc n))

chain-rel : {A A′ : Set} (R : A → A′ → Set) (S : A → A) (S′ : A′ → A′) (a : A) (a′ : A′)
          → R a a′ → ((z : A) (z′ : A′) → R z z′ → R (S z) (S′ z′)) → (n : ℕ) → R (iter S a n) (G.iter S′ a′ n)
chain-rel R S S′ a a′ ra hS zero    = ra
chain-rel R S S′ a a′ ra hS (suc n) = hS _ _ (chain-rel R S S′ a a′ ra hS n)

lc-rel : {A A′ : Set} (R : A → A′ → Set) (j : L) (j′ : F.L) (q : Lr j j′)
         (Φ : A → Tr j) (Φ′ : A′ → F.Tr j′) (S : A → A) (S′ : A′ → A′) (a : A) (a′ : A′)
       → R a a′ → ((z : A) (z′ : A′) → R z z′ → R (S z) (S′ z′))
       → ((z : A) (z′ : A′) → R z z′ → Rel j j′ q (Φ z) (Φ′ z′))
       → Rel j j′ q (lim (cum (λ n → Φ (iter S a n)))) (F.lim (G.cum (λ n → Φ′ (G.iter S′ a′ n))))
lc-rel R j j′ q Φ Φ′ S S′ a a′ ra hS hΦ =
  _ , refl , cum-rel j j′ q _ _ (λ n → hΦ _ _ (chain-rel R S S′ a a′ ra hS n))

Ωt-rel : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) → Rel ℓ ℓ′ r (Ωt ℓ) (G.Ωt ℓ′)
Ωt-rel zero     .F.zero      refl = F.zero , refl , refl
Ωt-rel (suc a)  .(F.suc a′) (a′ , refl , r) = _ , refl , λ z z′ rz → F.zero , _ , refl , refl , z′ , refl , rz
Ωt-rel (lim g)  .(F.lim g′) (g′ , refl , r) = _ , refl , cl
  where
  cl : (n : ℕ) → Rel (lim g) (F.lim g′) (g′ , refl , r) (seq (Ωt (lim g)) n) (GL.seq (G.Ωt (F.lim g′)) n)
  cl zero    = _ , _ , refl , refl , Ωt-rel (g zero) (g′ zero) (r zero)
  cl (suc n) = _ , _ , refl , cl n , Ωt-rel (g (suc n)) (g′ (suc n)) (r (suc n))
Ωt-rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) =
  _ , refl , λ z z′ rz → F.zero , z′ , rz , _ , refl , refl , Ωt-rel (h z) (h′ z′) (rh z z′ rz)

B₀-rel : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) → RelB ℓ ℓ′ r (B₀ ℓ) (G.B₀ ℓ′)
B₀-rel ℓ ℓ′ r = Ωt-rel zero F.zero refl , λ {j} {j′} {w} {w′} {q} _ → Ωt-rel j j′ q

eqℕ-dec : (m n : ℕ) → (Σ (m ≡ n) λ e → (eqℕ m n ≡ just e) × (G.eqℕ m n ≡ just e))
                    ⊎ ((eqℕ m n ≡ nothing) × (G.eqℕ m n ≡ nothing))
eqℕ-dec zero    zero    = inj₁ (refl , refl , refl)
eqℕ-dec zero    (suc n) = inj₂ (refl , refl)
eqℕ-dec (suc m) zero    = inj₂ (refl , refl)
eqℕ-dec (suc m) (suc n) with eqℕ-dec m n
... | inj₁ (refl , e₁ , e₂) rewrite e₁ | e₂ = inj₁ (refl , refl , refl)
... | inj₂ (e₁ , e₂)        rewrite e₁ | e₂ = inj₂ (refl , refl)
```

## 4 两种折叠保持对应

```agda
mutual
  rel⊥ : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) (B : Base ℓ) (B′ : G.Base ℓ′) → RelB ℓ ℓ′ r B B′
       → (x : Tr ℓ) (x′ : F.Tr ℓ′) → Rel ℓ ℓ′ r x x′ → Rel zero F.zero refl (ψ⊥ ℓ B x) (G.ψ⊥ ℓ′ B′ x′)
  rel⊥ ℓ ℓ′ r B B′ hB zero    .F.zero      refl = proj₁ hB
  rel⊥ ℓ ℓ′ r B B′ hB (suc x) .(F.suc x′) (x′ , refl , rx) =
    next-rel zero F.zero refl _ _ (rel⊥ ℓ ℓ′ r B B′ hB x x′ rx)
  rel⊥ ℓ ℓ′ r B B′ hB (lim f) .(F.lim f′) (f′ , refl , rf) =
    _ , refl , λ n → rel⊥ ℓ ℓ′ r B B′ hB (f n) (f′ n) (rf n)
  rel⊥ (suc a) .(F.suc a′) (a′ , refl , r) B B′ hB (Ω _ g) .(F.Ω (inj₁ tt) g′) (g′ , refl , rg) =
    lc-rel (Rel a a′ r) zero F.zero refl (λ z → ψ⊥ (suc a) B (g z)) (λ z′ → G.ψ⊥ (F.suc a′) B′ (g′ z′))
      _ _ zero F.zero refl
      (λ z z′ rz → rels (suc a) (F.suc a′) (a′ , refl , r) B B′ hB (wins wself) (g z) (g′ z′) (rg z z′ rz))
      (λ z z′ rz → rel⊥ (suc a) (F.suc a′) (a′ , refl , r) B B′ hB (g z) (g′ z′) (rg z z′ rz))
  rel⊥ (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB (Ω _ g) .(F.Ω (inj₁ (inj₁ tt)) g′) (g′ , refl , rg) =
    lc-rel (Rel k k′ r) zero F.zero refl (λ z → ψ⊥ (Ωₗ k h) B (g z)) (λ z′ → G.ψ⊥ (F.Ωₗ k′ h′) B′ (g′ z′))
      _ _ zero F.zero refl
      (λ z z′ rz → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (wink wself) (g z) (g′ z′) (rg z z′ rz))
      (λ z z′ rz → rel⊥ (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (g z) (g′ z′) (rg z z′ rz))
  rel⊥ zero    _ _ _ _ _ (Ω () _) _ _
  rel⊥ (lim _) _ _ _ _ _ (Ω () _) _ _
  rel⊥ (suc a) .(F.suc a′) (a′ , refl , r) B B′ hB (up x _ y) .(F.up x″ tt y′) (x″ , y′ , refl , rx , ry) =
    rel⊥ a a′ r (dS a B x) (GL.dS a′ B′ x″)
      (rel⊥ (suc a) (F.suc a′) _ B B′ hB x x″ rx , λ ρ → rels (suc a) (F.suc a′) _ B B′ hB (wins ρ) x x″ rx) y y′ ry
  rel⊥ (lim g) .(F.lim g′) (g′ , refl , r) B B′ hB (up x n y) .(F.up x″ n y′) (x″ , y′ , refl , rx , ry) =
    rel⊥ (g n) (g′ n) (r n) (dL g B n x) (GL.dL g′ B′ n x″)
      (rel⊥ (lim g) (F.lim g′) _ B B′ hB x x″ rx , λ ρ → rels (lim g) (F.lim g′) _ B B′ hB (winl ρ) x x″ rx) y y′ ry
  rel⊥ (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB (up x c y) .(F.up x″ c′ y′)
       (x″ , c′ , rc , y′ , refl , rx , ry) =
    rel⊥ (h c) (h′ c′) (rh c c′ rc) (dW k h B c x) (GL.dW k′ h′ B′ c′ x″)
      (rel⊥ (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB x x″ rx , λ ρ → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (winb rc ρ) x x″ rx)
      y y′ ry
  rel⊥ zero _ _ _ _ _ (up _ () _) _ _

  rels : (ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) (B : Base ℓ) (B′ : G.Base ℓ′) → RelB ℓ ℓ′ r B B′
       → {j : L} {j′ : F.L} {w : j ≤ ℓ} {w′ : j′ G.≤ ℓ′} {q : Lr j j′} → Wr r w w′ q
       → (x : Tr ℓ) (x′ : F.Tr ℓ′) → Rel ℓ ℓ′ r x x′ → Rel j j′ q (ψs ℓ B j w x) (G.ψs ℓ′ B′ j′ w′ x′)
  rels ℓ ℓ′ r B B′ hB ρ zero .F.zero refl = proj₂ hB ρ
  rels ℓ ℓ′ r B B′ hB {j} {j′} {q = q} ρ (suc x) .(F.suc x′) (x′ , refl , rx) =
    next-rel j j′ q _ _ (rels ℓ ℓ′ r B B′ hB ρ x x′ rx)
  rels ℓ ℓ′ r B B′ hB ρ (lim f) .(F.lim f′) (f′ , refl , rf) =
    _ , refl , λ n → rels ℓ ℓ′ r B B′ hB ρ (f n) (f′ n) (rf n)
  rels (suc a) .(F.suc a′) (a′ , refl , r) B B′ hB wself (Ω _ g) .(F.Ω (inj₁ tt) g′) (g′ , refl , rg) =
    _ , refl , λ z z′ rz → rels (suc a) (F.suc a′) _ B B′ hB wself (g z) (g′ z′) (rg z z′ rz)
  rels (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB wself (Ω _ g) .(F.Ω (inj₁ (inj₁ tt)) g′) (g′ , refl , rg) =
    _ , refl , λ z z′ rz → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB wself (g z) (g′ z′) (rg z z′ rz)
  rels (suc a) .(F.suc a′) (a′ , refl , r) B B′ hB {j} {j′} {q = q} (wins {w = w} {w′ = w′} ρ)
       (Ω _ g) .(F.Ω (inj₁ tt) g′) (g′ , refl , rg) =
    lc-rel (Rel a a′ r) j j′ q (λ z → ψs (suc a) B j (ins w) (g z)) (λ z′ → G.ψs (F.suc a′) B′ j′ (G.ins w′) (g′ z′))
      _ _ zero F.zero refl
      (λ z z′ rz → rels (suc a) (F.suc a′) _ B B′ hB (wins wself) (g z) (g′ z′) (rg z z′ rz))
      (λ z z′ rz → rels (suc a) (F.suc a′) _ B B′ hB (wins ρ) (g z) (g′ z′) (rg z z′ rz))
  rels (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB {j} {j′} {q = q} (wink {w = w} {w′ = w′} ρ)
       (Ω _ g) .(F.Ω (inj₁ (inj₁ tt)) g′) (g′ , refl , rg) =
    lc-rel (Rel k k′ r) j j′ q (λ z → ψs (Ωₗ k h) B j (ink w) (g z)) (λ z′ → G.ψs (F.Ωₗ k′ h′) B′ j′ (G.ink w′) (g′ z′))
      _ _ zero F.zero refl
      (λ z z′ rz → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (wink wself) (g z) (g′ z′) (rg z z′ rz))
      (λ z z′ rz → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (wink ρ) (g z) (g′ z′) (rg z z′ rz))
  rels (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB {j} {j′} {q = q}
       (winb {c = c} {c′ = c′} rc {w = w} {w′ = w′} ρ) (Ω _ g) .(F.Ω (inj₁ (inj₁ tt)) g′) (g′ , refl , rg) =
    lc-rel (Rel k k′ r) j j′ q (λ z → ψs (Ωₗ k h) B j (inb c w) (g z))
      (λ z′ → G.ψs (F.Ωₗ k′ h′) B′ j′ (G.inb c′ w′) (g′ z′))
      _ _ zero F.zero refl
      (λ z z′ rz → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (wink wself) (g z) (g′ z′) (rg z z′ rz))
      (λ z z′ rz → rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (winb rc ρ) (g z) (g′ z′) (rg z z′ rz))
  rels zero    _ _ _ _ _ _ (Ω () _) _ _
  rels (lim _) _ _ _ _ _ _ (Ω () _) _ _
  rels (suc a) .(F.suc a′) (a′ , refl , r) B B′ hB wself (up x _ y) .(F.up x″ tt y′) (x″ , y′ , refl , rx , ry) =
    _ , _ , refl , rels (suc a) (F.suc a′) _ B B′ hB wself x x″ rx , ry
  rels (lim g) .(F.lim g′) (g′ , refl , r) B B′ hB wself (up x n y) .(F.up x″ n y′) (x″ , y′ , refl , rx , ry) =
    _ , _ , refl , rels (lim g) (F.lim g′) _ B B′ hB wself x x″ rx , ry
  rels (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB wself (up x c y) .(F.up x″ c′ y′)
       (x″ , c′ , rc , y′ , refl , rx , ry) =
    _ , _ , rc , _ , refl , rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB wself x x″ rx , ry
  rels zero _ _ _ _ _ _ (up _ () _) _ _
  rels (suc a) .(F.suc a′) (a′ , refl , r) B B′ hB (wins ρ) (up x _ y) .(F.up x″ tt y′) (x″ , y′ , refl , rx , ry) =
    rels a a′ r (dS a B x) (GL.dS a′ B′ x″)
      (rel⊥ (suc a) (F.suc a′) _ B B′ hB x x″ rx , λ ρ′ → rels (suc a) (F.suc a′) _ B B′ hB (wins ρ′) x x″ rx) ρ y y′ ry
  rels (lim g) .(F.lim g′) (g′ , refl , r) B B′ hB {j} {j′} {q = q} (winl {n = n} ρ) (up x m y) .(F.up x″ m y′)
       (x″ , y′ , refl , rx , ry) with eqℕ-dec m n
  ... | inj₁ (refl , e₁ , e₂) rewrite e₁ | e₂ =
    rels _ _ _ (dL g B m x) (GL.dL g′ B′ m x″)
      (rel⊥ (lim g) (F.lim g′) _ B B′ hB x x″ rx , λ ρ′ → rels (lim g) (F.lim g′) _ B B′ hB (winl ρ′) x x″ rx) ρ y y′ ry
  ... | inj₂ (e₁ , e₂) rewrite e₁ | e₂ =
    +-rel j j′ q _ _ (rels (lim g) (F.lim g′) _ B B′ hB (winl ρ) x x″ rx)
      (ι-rel j j′ q _ _ (rel⊥ (g m) (g′ m) (r m) (B₀ _) (G.B₀ _) (B₀-rel _ _ _) y y′ ry))
  rels (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB {j} {j′} {q = q} (wink ρ) (up x c y) .(F.up x″ c′ y′)
       (x″ , c′ , rc , y′ , refl , rx , ry) =
    +-rel j j′ q _ _ (rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (wink ρ) x x″ rx)
      (ι-rel j j′ q _ _ (rel⊥ (h c) (h′ c′) (rh c c′ rc) (B₀ _) (G.B₀ _) (B₀-rel _ _ _) y y′ ry))
  rels (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) B B′ hB {j} {j′} {q = q} (winb rc₀ ρ) (up x c y) .(F.up x″ c′ y′)
       (x″ , c′ , rc , y′ , refl , rx , ry) =
    +-rel j j′ q _ _ (rels (Ωₗ k h) (F.Ωₗ k′ h′) _ B B′ hB (winb rc₀ ρ) x x″ rx)
      (ι-rel j j′ q _ _ (rel⊥ (h c) (h′ c′) (rh c c′ rc) (B₀ _) (G.B₀ _) (B₀-rel _ _ _) y y′ ry))
```

## 5 塔, Λ 与读法 ψ₀(Λ) 的闭项相对应

```agda
⊕-rel : (a : L) (a′ : F.L) (b : L) (b′ : F.L) → Lr a a′ → Lr b b′ → Lr (a ⊕ b) (a′ F.⊕ b′)
⊕-rel a a′ zero     .F.zero         ra refl = ra
⊕-rel a a′ (suc b)  .(F.suc b′)    ra (b′ , refl , rb) = _ , refl , ⊕-rel a a′ b b′ ra rb
⊕-rel a a′ (lim g)  .(F.lim g′)    ra (g′ , refl , rg) = _ , refl , λ n → ⊕-rel a a′ (g n) (g′ n) ra (rg n)
⊕-rel a a′ (Ωₗ k h) .(F.Ωₗ k′ h′) ra (k′ , h′ , refl , rk , rh) =
  k′ , _ , refl , rk , λ c c′ rc → ⊕-rel a a′ (h c) (h′ c′) ra (rh c c′ rc)

↑-rel : (k : L) (k′ : F.L) (r : Lr k k′) (c : Tr k) (c′ : F.Tr k′) → Rel k k′ r c c′ → Lr (↑ k c) (F.↑ k′ c′)
↑-rel k k′ r zero    .F.zero      refl = refl
↑-rel k k′ r (suc x) .(F.suc x′) (x′ , refl , rx) = _ , refl , ↑-rel k k′ r x x′ rx
↑-rel k k′ r (lim f) .(F.lim f′) (f′ , refl , rf) = _ , refl , λ n → ↑-rel k k′ r (f n) (f′ n) (rf n)
↑-rel (suc a) .(F.suc a′) (a′ , refl , r) (Ω _ g) .(F.Ω (inj₁ tt) g′) (g′ , refl , rg) =
  a′ , _ , refl , r , λ c c′ rc → ↑-rel (suc a) (F.suc a′) _ (g c) (g′ c′) (rg c c′ rc)
↑-rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (Ω _ g) .(F.Ω (inj₁ (inj₁ tt)) g′) (g′ , refl , rg) =
  k′ , _ , refl , r , λ c c′ rc → ↑-rel (Ωₗ k h) (F.Ωₗ k′ h′) _ (g c) (g′ c′) (rg c c′ rc)
↑-rel zero    _ _ (Ω () _) _ _
↑-rel (lim _) _ _ (Ω () _) _ _
↑-rel (suc a) .(F.suc a′) (a′ , refl , r) (up x _ y) .(F.up x″ tt y′) (x″ , y′ , refl , rx , ry) =
  ⊕-rel _ _ _ _ (↑-rel (suc a) (F.suc a′) _ x x″ rx) (↑-rel a a′ r y y′ ry)
↑-rel (lim g) .(F.lim g′) (g′ , refl , r) (up x n y) .(F.up x″ n y′) (x″ , y′ , refl , rx , ry) =
  ⊕-rel _ _ _ _ (↑-rel (lim g) (F.lim g′) _ x x″ rx) (↑-rel (g n) (g′ n) (r n) y y′ ry)
↑-rel (Ωₗ k h) .(F.Ωₗ k′ h′) (k′ , h′ , refl , r , rh) (up x c y) .(F.up x″ c′ y′) (x″ , c′ , rc , y′ , refl , rx , ry) =
  ⊕-rel _ _ _ _ (↑-rel (Ωₗ k h) (F.Ωₗ k′ h′) _ x x″ rx) (↑-rel (h c) (h′ c′) (rh c c′ rc) y y′ ry)
↑-rel zero _ _ (up _ () _) _ _

tw-rel : (n : ℕ) → Lr (tw n) (F.tw n)
tw-rel zero    = refl
tw-rel (suc n) =
  F.tw n , _ , refl , tw-rel n , λ c c′ rc → ⊕-rel (tw n) (F.tw n) _ _ (tw-rel n) (↑-rel (tw n) (F.tw n) (tw-rel n) c c′ rc)

Λ-rel : Lr Λ F.Λ
Λ-rel = F.tw , refl , tw-rel

EBO-rel : Rel zero F.zero refl EBOᶜ GL.EBOᶜ
EBO-rel = rel⊥ Λ F.Λ Λ-rel (B₀ Λ) (G.B₀ F.Λ) (B₀-rel Λ F.Λ Λ-rel) (Ωt Λ) (G.Ωt F.Λ) (Ωt-rel Λ F.Λ Λ-rel)
```
