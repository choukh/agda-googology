# 折叠带证据 (F1 原型): 折叠与 "输出带证据" 互递归

> 判决: 原型, 停机通过. 折叠 `ψ⊥`, `ψs` 多带树的证据 `E ℓ x`; `Ωₗ` 层取孩子层路线时用证据里孩子下标的证据 (`proj₂ ρ c ec`), 不再用裸的 c. 链步回灌的分支要带证据, 所以折叠与 `pres⊥`, `press` (输出带证据且非零) 在同一个互递归块里.
> 两处退让: 保留行的分支是裸的, 只能取 `E₀` (`EBr₀`); ℕ 极限逐项折叠的输出不给相邻序 (`nothing`), 因为那要单调性, 而两项的证据互相独立 (见 `YiFLCheck.dep`).
> 不否定什么. 其余各行与 `YiLimFold` 逐行对应; 底与目标的底都带 "证据且非零". 测试与依赖性的定理在 `YiFLCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFLFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃t; +-mono; ι-mono; Ωt-nz; Ωt-leg; seq)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpLegal using (Up-mono)
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiFLBlock
```

## 带证据且非零

```agda
EN : (j : L) → Tr j → Set
EN j t = E j t × (j ⊢ zero ◃ t)

T⁺ : L → Set
T⁺ j = Σ (Tr j) (EN j)

BE : (ℓ : L) → Base ℓ → Set
BE ℓ B = EN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → EN j (bs B j w))

Bs : L → Set
Bs ℓ = Σ (Base ℓ) (BE ℓ)

bs⁺ : ∀ {ℓ} → Bs ℓ → (j : L) → j ≤ ℓ → T⁺ j
bs⁺ B j w = bs (proj₁ B) j w , proj₂ (proj₂ B) j w

+-E : ∀ {ℓ} (a b : Tr ℓ) → E ℓ a → E ℓ b → E ℓ (a + b)
+-E a zero       ea eb = ea
+-E a (suc b)    ea eb = +-E a b ea eb
+-E a (lim f)    ea (ef , A) = (λ n → +-E a (f n) ea (ef n)) , mapᴹ (λ d n → +-mono a (d n)) A
+-E a (Ω p g)    ea (ep , eg) = ep , λ z ez → +-E a (g z) ea (eg z ez)
+-E a (up y c w) ea (ey , ei , ew) = +-E a y ea ey , ei , ew

ι-E : (j : L) (a : Tr zero) → E zero a → E j (ι j a)
ι-E j zero    e = tt
ι-E j (suc a) e = ι-E j a e
ι-E j (lim f) (ef , A) = (λ n → ι-E j (f n) (ef n)) , mapᴹ (λ d n → ι-mono j (d n)) A
ι-E j (Ω () _) e
ι-E j (up _ () _) e

nextEN : ∀ {j} (b : Tr j) → EN j b → EN j (next b)
nextEN {j} b (eb , zb) = (il , just ia) , ◃t zb (◃l zero)
  where
  il : (n : ℕ) → E j (iter (b +_) b n)
  il zero    = eb
  il (suc n) = +-E b _ eb (il n)
  ia : (n : ℕ) → j ⊢ iter (b +_) b n ◃ iter (b +_) b (suc n)
  ia zero    = +-mono b zb
  ia (suc n) = +-mono b (ia n)

cumEN : ∀ {j} (F : ℕ → Tr j) → ((n : ℕ) → EN j (F n)) → EN j (lim (cum F))
cumEN {j} F hF = (cl , just (λ n → +-mono (cum F n) (proj₂ (hF (suc n))))) , ◃t (proj₂ (hF zero)) (◃l zero)
  where
  cl : (n : ℕ) → E j (cum F n)
  cl zero    = proj₁ (hF zero)
  cl (suc n) = +-E (cum F n) (F (suc n)) (cl n) (proj₁ (hF (suc n)))

fbEN : ∀ {j} (b : Tr j) → EN j b → (t : Tr zero) → EN zero t → EN j (b + ι j t)
fbEN {j} b (eb , zb) t (et , zt) = +-E b (ι j t) eb (ι-E j t et) , ◃t zb (+-mono b (ι-mono j zt))

Ωt-E : (ℓ : L) → E ℓ (Ωt ℓ)
Ωt-E zero     = tt
Ωt-E (suc a)  = tt , λ z ez → tt , tt , ez
Ωt-E (lim g)  = cl , just (proj₂ (Ωt-leg (lim g)))
  where
  cl : (n : ℕ) → E (lim g) (seq (Ωt (lim g)) n)
  cl zero    = tt , tt , Ωt-E (g zero)
  cl (suc n) = cl n , tt , Ωt-E (g (suc n))
Ωt-E (Ωₗ k h) = tt , λ c ec → tt , ec , Ωt-E (h c)

B₀⁺ : (ℓ : L) → Bs ℓ
B₀⁺ ℓ = B₀ ℓ , (Ωt-E zero , Ωt-nz zero) , λ j _ → Ωt-E j , Ωt-nz j
```

## 上折保持 "带证据且非零"

下行链里的孩子下标带证据 (`DnE`), 搬进本层的槽位才有证据.

```agda
DnE : ∀ {ℓ j} → Dn ℓ j → Set
DnE stop           = ⊤
DnE (down {j} d c) = DnE d × EI j c

chPE : (j : L) (c : Ch j) → EI j c → (p : Pos (chL j c)) → EP (chL j c) p → EP j (chP j c p)
chPE (suc a)  _ _  p e = e
chPE (lim g)  n _  p e = e
chPE (Ωₗ k h) c ei p e = ei , e

mvE : ∀ {ℓ j} (d : Dn ℓ j) → DnE d → (p : Pos j) → EP j p → EP ℓ (mv d p)
mvE stop           _         p e = e
mvE (down {j} d c) (de , ei) p e = mvE d de (chP j c p) (chPE j c ei p e)

chBrE : (j : L) (c : Ch j) (p : Pos (chL j c)) (z : Br j (chP j c p))
  → EBr j (chP j c p) z → EBr (chL j c) p (chBr j c p z)
chBrE (suc a)  _ p z e = e
chBrE (lim g)  n p z e = e
chBrE (Ωₗ k h) c p z e = e

mvBrE : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) (z : Br ℓ (mv d p)) → EBr ℓ (mv d p) z → EBr j p (mvBr d p z)
mvBrE stop           p z e = e
mvBrE (down {j} d c) p z e = chBrE j c p _ (mvBrE d (chP j c p) z e)

Up-EN : ∀ {ℓ} (j : L) (d : Dn ℓ j) → DnE d → (b : Tr ℓ) → EN ℓ b → (y : Tr j) → E j y → EN ℓ (Up j d b y)
Up-EN j d de b hb zero    e = hb
Up-EN j d de b hb (suc y) e = nextEN _ (Up-EN j d de b hb y e)
Up-EN j d de b hb (lim f) (ef , A) =
  ((λ n → proj₁ (Up-EN j d de b hb (f n) (ef n))) , mapᴹ (λ a n → Up-mono j d b (a n)) A)
  , ◃t (proj₂ (Up-EN j d de b hb (f zero) (ef zero))) (◃l zero)
Up-EN {ℓ} j d de b hb (Ω p g) (ep , eg) =
  (mvE d de p ep , λ z ez → proj₁ (Up-EN j d de b hb (g (mvBr d p z)) (eg _ (mvBrE d p z ez))))
  , ◃t (proj₂ (Up-EN j d de b hb (g (mvBr d p (fromBr ℓ (mv d p) zero)))
                (eg _ (mvBrE d p _ (eFrom ℓ (mv d p) zero tt))))) ◃w
Up-EN (suc a)  d de b hb (up y _ y′) (ey , _ , ey′) =
  Up-EN a (down d tt) (de , tt) _ (Up-EN (suc a) d de b hb y ey) y′ ey′
Up-EN (lim g)  d de b hb (up y n y′) (ey , _ , ey′) =
  Up-EN (g n) (down d n) (de , tt) _ (Up-EN (lim g) d de b hb y ey) y′ ey′
Up-EN (Ωₗ k h) d de b hb (up y c y′) (ey , ei , ey′) =
  Up-EN (h c) (down d c) (de , ei) _ (Up-EN (Ωₗ k h) d de b hb y ey) y′ ey′
Up-EN zero     d de b hb (up y () _)
```

## 保留判定

与 `YiLimFold.kp` 逐行对应. 多带槽位的证据: 槽位在分支侧 `inj₂ (c , t)` 时孩子层的路线取 `ρc c ec`; 保留时把搬到目标层的槽位的证据交给 K.
目标路径里的下标 (`inb c w`) 没有证据, 取 `E₀` (已知退让).

```agda
mutual
  kp : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (p : Pos ℓ) → EP ℓ p → {j : L} (w : j ≤ ℓ) {X : Set}
     → ((q : Pos j) → EP j q → (Br j q → Br ℓ p) → X) → X → X
  kp ℓ        ε ρ p ep self      K d = K p ep (λ z → z)
  kp (suc a)  ε ρ p ep (ins w)   K d = kp⁼ a ε ρ p ep w K d
  kp (lim g)  ε (ρc , R) (m , p) ep (inl n w) K d =
    caseW (way g R m n)
      (λ v → kp⁼ (g n) (ε n) (ρc n) (psh v p) (pshE v p ep) w (λ q eq cv → K q eq (λ z → pshBr v p (cv z))) d)
      (λ v → kp⁼ (g m) (ε m) (ρc m) p ep (w ∙ v) K d)
      d
  kp (lim g)  ε (ρc , R) (m , p) ep (inlu ws) K d = kp⁼ (g m) (ε m) (ρc m) p ep (ws m) K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t) ep (ink w) K d = kp⁼ k ek ρk t ep w K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t) ep (inb c w) K d =
    kp⁼ (h c) (proj₂ (e c)) (ρc c (E₀ k c)) (psh (proj₁ (e c)) t) (pshE (proj₁ (e c)) t ep) w
      (λ q eq cv → K q eq (λ z → pshBr (proj₁ (e c)) t (cv z))) d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t) ep (inu ws) K d =
    kp⁼ (h zero) (proj₂ (e zero)) (ρc zero tt) (psh (proj₁ (e zero)) t) (pshE (proj₁ (e zero)) t ep) (ws zero)
      (λ q eq cv → K q eq (λ z → pshBr (proj₁ (e zero)) t (cv z))) d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ec , et) (ink w) K d =
    kp⁼ (h c) (proj₂ (e c)) (ρc c ec) t et (w ∙ proj₁ (e c)) K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ec , et) (inu ws) K d =
    kp⁼ (h c) (proj₂ (e c)) (ρc c ec) t et (ws c) K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) ep (inb c′ w) K d = d

  kp⁼ : (a : L) (ε : Ev a) (ρ : Rt′ a) (p : Pos⁼ a) → EP⁼ a p → {j : L} (w : j ≤ a) {X : Set}
      → ((q : Pos j) → EP j q → (Br j q → Br⁼ a p) → X) → X → X
  kp⁼ a ε ρ (inj₁ _) ep w K d = d
  kp⁼ a ε ρ (inj₂ p) ep w K d = kp a ε ρ p ep w K d

mutual
  kp-ind : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (p : Pos ℓ) (ep : EP ℓ p) {j : L} (w : j ≤ ℓ) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → EP j q → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (eq : EP j q) (cv : Br j q → Br ℓ p) → Q (K q eq cv)) → Q d
    → Q (kp ℓ ε ρ p ep w K d)
  kp-ind ℓ        ε ρ p ep self      Q hk hd = hk p ep (λ z → z)
  kp-ind (suc a)  ε ρ p ep (ins w)   Q hk hd = kp⁼-ind a ε ρ p ep w Q hk hd
  kp-ind (lim g)  ε (ρc , R) (m , p) ep (inl n w) Q hk hd =
    caseW-ind Q (way g R m n)
      (λ v → kp⁼-ind (g n) (ε n) (ρc n) (psh v p) (pshE v p ep) w Q (λ q eq cv → hk q eq (λ z → pshBr v p (cv z))) hd)
      (λ v → kp⁼-ind (g m) (ε m) (ρc m) p ep (w ∙ v) Q hk hd)
      hd
  kp-ind (lim g)  ε (ρc , R) (m , p) ep (inlu ws) Q hk hd = kp⁼-ind (g m) (ε m) (ρc m) p ep (ws m) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t) ep (ink w) Q hk hd = kp⁼-ind k ek ρk t ep w Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t) ep (inb c w) Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c (E₀ k c)) (psh (proj₁ (e c)) t) (pshE (proj₁ (e c)) t ep) w Q
      (λ q eq cv → hk q eq (λ z → pshBr (proj₁ (e c)) t (cv z))) hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t) ep (inu ws) Q hk hd =
    kp⁼-ind (h zero) (proj₂ (e zero)) (ρc zero tt) (psh (proj₁ (e zero)) t) (pshE (proj₁ (e zero)) t ep) (ws zero) Q
      (λ q eq cv → hk q eq (λ z → pshBr (proj₁ (e zero)) t (cv z))) hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ec , et) (ink w) Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c ec) t et (w ∙ proj₁ (e c)) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ec , et) (inu ws) Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c ec) t et (ws c) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) ep (inb c′ w) Q hk hd = hd

  kp⁼-ind : (a : L) (ε : Ev a) (ρ : Rt′ a) (p : Pos⁼ a) (ep : EP⁼ a p) {j : L} (w : j ≤ a) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → EP j q → (Br j q → Br⁼ a p) → X} {d : X}
    → ((q : Pos j) (eq : EP j q) (cv : Br j q → Br⁼ a p) → Q (K q eq cv)) → Q d
    → Q (kp⁼ a ε ρ p ep w K d)
  kp⁼-ind a ε ρ (inj₁ _) ep w Q hk hd = hd
  kp⁼-ind a ε ρ (inj₂ p) ep w Q hk hd = kp-ind a ε ρ p ep w Q hk hd
```

## 折叠与 "输出带证据" (互递归)

链: 分支连同它的证据一起迭代; 下一个分支是链步的折叠值, 它的证据是 `press` 对同一次调用的结论. 孩子的底的证据逐处内联 (与 `YiLimLegal.press` 同一个理由: 每次调用的层号字面不增).

```agda
mutual
  ψ⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (B : Bs ℓ) (x : Tr ℓ) → E ℓ x → Tr zero
  ψ⊥ ℓ ε ρ B zero    e = b⊥ (proj₁ B)
  ψ⊥ ℓ ε ρ B (suc x) e = next (ψ⊥ ℓ ε ρ B x e)
  ψ⊥ ℓ ε ρ B (lim f) e = lim (λ n → ψ⊥ ℓ ε ρ B (f n) (proj₁ e n))
  ψ⊥ ℓ ε ρ B (Ω p g) e = lim (cum (λ n → ψ⊥ ℓ ε ρ B (g (proj₁ (ch n))) (proj₂ e _ (proj₂ (ch n)))))
    where
    step : Σ (Br ℓ p) (EBr ℓ p) → Σ (Br ℓ p) (EBr ℓ p)
    step z = fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs⁺ B (at ℓ p) (posW ℓ p)) (g (proj₁ z)) (proj₂ e _ (proj₂ z)))
           , eFrom ℓ p _ (proj₁ (press ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs⁺ B (at ℓ p) (posW ℓ p)) (g (proj₁ z)) (proj₂ e _ (proj₂ z))))
    ch : ℕ → Σ (Br ℓ p) (EBr ℓ p)
    ch = iter step (fromBr ℓ p zero , eFrom ℓ p zero tt)
  ψ⊥ (suc a)  ε ρ B (up x _ y) e =
    ψ⊥ a ε ρ
      ( base (ψ⊥ (suc a) ε ρ B x (proj₁ e)) (λ j w → ψs (suc a) ε ρ B j (ins w) (bs⁺ B j (ins w)) x (proj₁ e))
      , pres⊥ (suc a) ε ρ B x (proj₁ e) , λ j w → press (suc a) ε ρ B j (ins w) (bs⁺ B j (ins w)) x (proj₁ e) )
      y (proj₂ (proj₂ e))
  ψ⊥ (lim g)  ε ρ B (up x n y) e =
    ψ⊥ (g n) (ε n) (proj₁ ρ n)
      ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j w → ψs (lim g) ε ρ B j (inl n w) (bs⁺ B j (inl n w)) x (proj₁ e))
      , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j w → press (lim g) ε ρ B j (inl n w) (bs⁺ B j (inl n w)) x (proj₁ e) )
      y (proj₂ (proj₂ e))
  ψ⊥ (Ωₗ k h) ε ρ B (up x c y) e =
    ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e)))
      ( base (ψ⊥ (Ωₗ k h) ε ρ B x (proj₁ e)) (λ j w → ψs (Ωₗ k h) ε ρ B j (inb c w) (bs⁺ B j (inb c w)) x (proj₁ e))
      , pres⊥ (Ωₗ k h) ε ρ B x (proj₁ e) , λ j w → press (Ωₗ k h) ε ρ B j (inb c w) (bs⁺ B j (inb c w)) x (proj₁ e) )
      y (proj₂ (proj₂ e))
  ψ⊥ zero     ε ρ B (up x () y) e

  ψs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (B : Bs ℓ) (j : L) → j ≤ ℓ → T⁺ j → (x : Tr ℓ) → E ℓ x → Tr j
  ψs ℓ ε ρ B j w β zero    e = proj₁ β
  ψs ℓ ε ρ B j w β (suc x) e = next (ψs ℓ ε ρ B j w β x e)
  ψs ℓ ε ρ B j w β (lim f) e = lim (λ n → ψs ℓ ε ρ B j w β (f n) (proj₁ e n))
  ψs ℓ ε ρ B j w β (Ω p g) e =
    kp ℓ ε ρ p (proj₁ e) w
      (λ q eq cv → Ω q (λ z → ψs ℓ ε ρ B j w β (g (cv z)) (proj₂ e (cv z) (EBr₀ ℓ p (cv z)))))
      (lim (cum (λ n → ψs ℓ ε ρ B j w β (g (proj₁ (ch n))) (proj₂ e _ (proj₂ (ch n))))))
    where
    step : Σ (Br ℓ p) (EBr ℓ p) → Σ (Br ℓ p) (EBr ℓ p)
    step z = fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs⁺ B (at ℓ p) (posW ℓ p)) (g (proj₁ z)) (proj₂ e _ (proj₂ z)))
           , eFrom ℓ p _ (proj₁ (press ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs⁺ B (at ℓ p) (posW ℓ p)) (g (proj₁ z)) (proj₂ e _ (proj₂ z))))
    ch : ℕ → Σ (Br ℓ p) (EBr ℓ p)
    ch = iter step (fromBr ℓ p zero , eFrom ℓ p zero tt)
  ψs ℓ ε ρ B _ self β (up x c y) e = Upc ℓ c (ψs ℓ ε ρ B ℓ self β x (proj₁ e)) y
  ψs (suc a) ε ρ B j (ins w) β (up x _ y) e =
    ψs a ε ρ
      ( base (ψ⊥ (suc a) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (suc a) ε ρ B j′ (ins w′) (bs⁺ B j′ (ins w′)) x (proj₁ e))
      , pres⊥ (suc a) ε ρ B x (proj₁ e) , λ j′ w′ → press (suc a) ε ρ B j′ (ins w′) (bs⁺ B j′ (ins w′)) x (proj₁ e) )
      j w (ψs (suc a) ε ρ B j (ins w) β x (proj₁ e) , press (suc a) ε ρ B j (ins w) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  ψs (lim g) ε ρ B j (inl n w) β (up x m y) e =
    caseW (way g (proj₂ ρ) m n)
      (λ v → ψs (g n) (ε n) (proj₁ ρ n)
        ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl n w′) (bs⁺ B j′ (inl n w′)) x (proj₁ e))
        , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j′ w′ → press (lim g) ε ρ B j′ (inl n w′) (bs⁺ B j′ (inl n w′)) x (proj₁ e) )
        j w (ψs (lim g) ε ρ B j (inl n w) β x (proj₁ e) , press (lim g) ε ρ B j (inl n w) β x (proj₁ e))
        (emb (g n) (ε n) v y) (embE (g n) (ε n) v y (proj₂ (proj₂ e))))
      (λ v → ψs (g m) (ε m) (proj₁ ρ m)
        ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e))
        , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j′ w′ → press (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e) )
        j (w ∙ v) (ψs (lim g) ε ρ B j (inl n w) β x (proj₁ e) , press (lim g) ε ρ B j (inl n w) β x (proj₁ e))
        y (proj₂ (proj₂ e)))
      (ψs (lim g) ε ρ B j (inl n w) β x (proj₁ e)
        + ι j (ψ⊥ (g m) (ε m) (proj₁ ρ m) (B₀⁺ (g m)) y (proj₂ (proj₂ e))))
  ψs (lim g) ε ρ B j (inlu ws) β (up x m y) e =
    ψs (g m) (ε m) (proj₁ ρ m)
      ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e))
      , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j′ w′ → press (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e) )
      j (ws m) (ψs (lim g) ε ρ B j (inlu ws) β x (proj₁ e) , press (lim g) ε ρ B j (inlu ws) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  ψs (Ωₗ k h) ε ρ B j (ink w) β (up x c y) e =
    ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e)))
      ( base (ψ⊥ (Ωₗ k h) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e))
      , pres⊥ (Ωₗ k h) ε ρ B x (proj₁ e) , λ j′ w′ → press (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e) )
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β x (proj₁ e) , press (Ωₗ k h) ε ρ B j (ink w) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  ψs (Ωₗ k h) ε ρ B j (inu ws) β (up x c y) e =
    ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e)))
      ( base (ψ⊥ (Ωₗ k h) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e))
      , pres⊥ (Ωₗ k h) ε ρ B x (proj₁ e) , λ j′ w′ → press (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e) )
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β x (proj₁ e) , press (Ωₗ k h) ε ρ B j (inu ws) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  ψs (Ωₗ k h) ε ρ B j (inb c′ w) β (up x c y) e =
    ψs (Ωₗ k h) ε ρ B j (inb c′ w) β x (proj₁ e)
      + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e))) (B₀⁺ (h c)) y (proj₂ (proj₂ e)))

  pres⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (B : Bs ℓ) (x : Tr ℓ) (e : E ℓ x) → EN zero (ψ⊥ ℓ ε ρ B x e)
  pres⊥ ℓ ε ρ B zero    e = proj₁ (proj₂ B)
  pres⊥ ℓ ε ρ B (suc x) e = nextEN _ (pres⊥ ℓ ε ρ B x e)
  pres⊥ ℓ ε ρ B (lim f) e =
    ((λ n → proj₁ (pres⊥ ℓ ε ρ B (f n) (proj₁ e n))) , nothing)
    , ◃t (proj₂ (pres⊥ ℓ ε ρ B (f zero) (proj₁ e zero))) (◃l zero)
  pres⊥ ℓ ε ρ B (Ω p g) e = cumEN _ (λ n → pres⊥ ℓ ε ρ B (g _) (proj₂ e _ _))
  pres⊥ (suc a)  ε ρ B (up x _ y) e =
    pres⊥ a ε ρ
      ( base (ψ⊥ (suc a) ε ρ B x (proj₁ e)) (λ j w → ψs (suc a) ε ρ B j (ins w) (bs⁺ B j (ins w)) x (proj₁ e))
      , pres⊥ (suc a) ε ρ B x (proj₁ e) , λ j w → press (suc a) ε ρ B j (ins w) (bs⁺ B j (ins w)) x (proj₁ e) )
      y (proj₂ (proj₂ e))
  pres⊥ (lim g)  ε ρ B (up x n y) e =
    pres⊥ (g n) (ε n) (proj₁ ρ n)
      ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j w → ψs (lim g) ε ρ B j (inl n w) (bs⁺ B j (inl n w)) x (proj₁ e))
      , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j w → press (lim g) ε ρ B j (inl n w) (bs⁺ B j (inl n w)) x (proj₁ e) )
      y (proj₂ (proj₂ e))
  pres⊥ (Ωₗ k h) ε ρ B (up x c y) e =
    pres⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e)))
      ( base (ψ⊥ (Ωₗ k h) ε ρ B x (proj₁ e)) (λ j w → ψs (Ωₗ k h) ε ρ B j (inb c w) (bs⁺ B j (inb c w)) x (proj₁ e))
      , pres⊥ (Ωₗ k h) ε ρ B x (proj₁ e) , λ j w → press (Ωₗ k h) ε ρ B j (inb c w) (bs⁺ B j (inb c w)) x (proj₁ e) )
      y (proj₂ (proj₂ e))
  pres⊥ zero     ε ρ B (up x () y) e

  press : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (B : Bs ℓ) (j : L) (w : j ≤ ℓ) (β : T⁺ j) (x : Tr ℓ) (e : E ℓ x)
        → EN j (ψs ℓ ε ρ B j w β x e)
  press ℓ ε ρ B j w β zero    e = proj₂ β
  press ℓ ε ρ B j w β (suc x) e = nextEN _ (press ℓ ε ρ B j w β x e)
  press ℓ ε ρ B j w β (lim f) e =
    ((λ n → proj₁ (press ℓ ε ρ B j w β (f n) (proj₁ e n))) , nothing)
    , ◃t (proj₂ (press ℓ ε ρ B j w β (f zero) (proj₁ e zero))) (◃l zero)
  press ℓ ε ρ B j w β (Ω p g) e =
    kp-ind ℓ ε ρ p (proj₁ e) w (EN j)
      (λ q eq cv →
        (eq , λ z ez → proj₁ (press ℓ ε ρ B j w β (g (cv z)) (proj₂ e (cv z) (EBr₀ ℓ p (cv z)))))
        , ◃t (proj₂ (press ℓ ε ρ B j w β (g (cv (fromBr j q zero)))
                      (proj₂ e (cv (fromBr j q zero)) (EBr₀ ℓ p (cv (fromBr j q zero)))))) ◃w)
      (cumEN _ (λ n → press ℓ ε ρ B j w β (g _) (proj₂ e _ _)))
  press ℓ ε ρ B _ self β (up x c y) e =
    Up-EN (chL ℓ c) (down stop c) (tt , proj₁ (proj₂ e)) _ (press ℓ ε ρ B ℓ self β x (proj₁ e))
      (chT ℓ c y) (chE ℓ c y (proj₂ (proj₂ e)))
  press (suc a) ε ρ B j (ins w) β (up x _ y) e =
    press a ε ρ
      ( base (ψ⊥ (suc a) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (suc a) ε ρ B j′ (ins w′) (bs⁺ B j′ (ins w′)) x (proj₁ e))
      , pres⊥ (suc a) ε ρ B x (proj₁ e) , λ j′ w′ → press (suc a) ε ρ B j′ (ins w′) (bs⁺ B j′ (ins w′)) x (proj₁ e) )
      j w (ψs (suc a) ε ρ B j (ins w) β x (proj₁ e) , press (suc a) ε ρ B j (ins w) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  press (lim g) ε ρ B j (inl n w) β (up x m y) e =
    caseW-ind (EN j) (way g (proj₂ ρ) m n)
      (λ v → press (g n) (ε n) (proj₁ ρ n)
        ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl n w′) (bs⁺ B j′ (inl n w′)) x (proj₁ e))
        , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j′ w′ → press (lim g) ε ρ B j′ (inl n w′) (bs⁺ B j′ (inl n w′)) x (proj₁ e) )
        j w (ψs (lim g) ε ρ B j (inl n w) β x (proj₁ e) , press (lim g) ε ρ B j (inl n w) β x (proj₁ e))
        (emb (g n) (ε n) v y) (embE (g n) (ε n) v y (proj₂ (proj₂ e))))
      (λ v → press (g m) (ε m) (proj₁ ρ m)
        ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e))
        , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j′ w′ → press (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e) )
        j (w ∙ v) (ψs (lim g) ε ρ B j (inl n w) β x (proj₁ e) , press (lim g) ε ρ B j (inl n w) β x (proj₁ e))
        y (proj₂ (proj₂ e)))
      (fbEN _ (press (lim g) ε ρ B j (inl n w) β x (proj₁ e)) _
        (pres⊥ (g m) (ε m) (proj₁ ρ m) (B₀⁺ (g m)) y (proj₂ (proj₂ e))))
  press (lim g) ε ρ B j (inlu ws) β (up x m y) e =
    press (g m) (ε m) (proj₁ ρ m)
      ( base (ψ⊥ (lim g) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e))
      , pres⊥ (lim g) ε ρ B x (proj₁ e) , λ j′ w′ → press (lim g) ε ρ B j′ (inl m w′) (bs⁺ B j′ (inl m w′)) x (proj₁ e) )
      j (ws m) (ψs (lim g) ε ρ B j (inlu ws) β x (proj₁ e) , press (lim g) ε ρ B j (inlu ws) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  press (Ωₗ k h) ε ρ B j (ink w) β (up x c y) e =
    press (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e)))
      ( base (ψ⊥ (Ωₗ k h) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e))
      , pres⊥ (Ωₗ k h) ε ρ B x (proj₁ e) , λ j′ w′ → press (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e) )
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β x (proj₁ e) , press (Ωₗ k h) ε ρ B j (ink w) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  press (Ωₗ k h) ε ρ B j (inu ws) β (up x c y) e =
    press (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e)))
      ( base (ψ⊥ (Ωₗ k h) ε ρ B x (proj₁ e)) (λ j′ w′ → ψs (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e))
      , pres⊥ (Ωₗ k h) ε ρ B x (proj₁ e) , λ j′ w′ → press (Ωₗ k h) ε ρ B j′ (inb c w′) (bs⁺ B j′ (inb c w′)) x (proj₁ e) )
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β x (proj₁ e) , press (Ωₗ k h) ε ρ B j (inu ws) β x (proj₁ e))
      y (proj₂ (proj₂ e))
  press (Ωₗ k h) ε ρ B j (inb c′ w) β (up x c y) e =
    fbEN _ (press (Ωₗ k h) ε ρ B j (inb c′ w) β x (proj₁ e)) _
      (pres⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c (proj₁ (proj₂ e))) (B₀⁺ (h c)) y (proj₂ (proj₂ e)))

ψ₀ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt′ ℓ) (x : Tr ℓ) → E ℓ x → Tr zero
ψ₀ ℓ ε ρ = ψ⊥ ℓ ε ρ (B₀⁺ ℓ)
```
