# 重述后的关系在结点保留支上仍太宽: 无名下标上的分支不受约束

> 判决: 编译定理, 条件 (排中律作模块参数), 验收侧. 树 `xw` (第 1 层的结点, 下标有名字时分支是 `Ωt one` 的分支, 无名字时是同值的 "假后继" 树) 在 `YiNPName` 的关系下名为 Ω₁ (`named-xw`), 朝第 1 层折它的输出与项模型里 ψ₁(Ω₁) 的严格值不同, 所以 `BRow` 在 `xw` 上不成立 (`B-keep-false`); 前提 (目标层, 底值, 底族在第 1 层) 都是定理.
> 机制: 保留支的输出是结点, 严格值对一切下标取上确界; 命名关系的结点一行只约束有名字的下标, 而有名字的第 0 层的树的值有可数上界 (`c*`, 用项的枚举 `cover`).
> 不否定什么: `xw` 用排中律按 "有没有名字" 分情况定义, 不在塔与 Λ 的折叠里出现; 读作结点一行太宽, 不读作路线否定. 走链支不受影响 (链点都有名字).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNPWild where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
import Data.Nat.Properties as ℕP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Induction.WellFounded using (Acc; acc)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRVLevel
open import OCF.Lean.YiNMSharp
open import OCF.Lean.YiNMTerm
open import OCF.Lean.YiNMName using (cof-sucT; pred-sucT; ≈ᴸ-sym)
open import OCF.Lean.YiNMAbsorb using (one; o₁)
open import OCF.Lean.YiNPName
import OCF.Align.EboLeanDef as E
import OCF.Align.EBO as E0
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTrian as ET
import OCF.Align.EboBach as EBa
open EB using (NF; _≤ᵀ_)
```

## 记号的项可数

`gen n`: 嵌套深度不超过 n 的项 (列表). `cover`: 每个项都在某个 `gen n` 里.

```agda
gen : ℕ → List E.T
gen zero    = [] ∷ []
gen (suc n) = gen n ++ concatMap (λ u → concatMap (λ a → map (λ xs → E.ψ u a ∷ xs) (gen n)) (gen n)) (gen n)

∈ˡ : ∀ {A : Set} {x : A} {xs} ys → x ∈ xs → x ∈ (xs ++ ys)
∈ˡ ys (here e)  = here e
∈ˡ ys (there i) = there (∈ˡ ys i)

∈ʳ : ∀ {A : Set} {x : A} xs {ys} → x ∈ ys → x ∈ (xs ++ ys)
∈ʳ []       i = i
∈ʳ (_ ∷ xs) i = there (∈ʳ xs i)

∈m : ∀ {A B : Set} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
∈m f (here refl) = here refl
∈m f (there i)   = there (∈m f i)

∈c : ∀ {A B : Set} (f : A → List B) {x xs y} → x ∈ xs → y ∈ f x → y ∈ concatMap f xs
∈c f {xs = _ ∷ xs} (here refl) j = ∈ˡ (concatMap f xs) j
∈c f {xs = z ∷ xs} (there i)   j = ∈ʳ (f z) (∈c f i j)

lift′ : ∀ {t m n} → m ≤′ n → t ∈ gen m → t ∈ gen n
lift′ ≤′-refl     i = i
lift′ (≤′-step l) i = ∈ˡ _ (lift′ l i)

cover : (t : E.T) → Σ ℕ λ n → t ∈ gen n
cover [] = zero , here refl
cover (E.ψ u a ∷ xs) with cover u | cover a | cover xs
... | n₁ , i₁ | n₂ , i₂ | n₃ , i₃ =
  suc N , ∈ʳ (gen N) (∈c _ (lift′ l₁ i₁) (∈c _ (lift′ l₂ i₂) (∈m _ (lift′ l₃ i₃))))
  where
  N : ℕ
  N = n₁ ⊔ (n₂ ⊔ n₃)
  l₁ : n₁ ≤′ N
  l₁ = ℕP.≤⇒≤′ (ℕP.m≤m⊔n n₁ (n₂ ⊔ n₃))
  l₂ : n₂ ≤′ N
  l₂ = ℕP.≤⇒≤′ (ℕP.≤-trans (ℕP.m≤m⊔n n₂ n₃) (ℕP.m≤n⊔m n₁ (n₂ ⊔ n₃)))
  l₃ : n₃ ≤′ N
  l₃ = ℕP.≤⇒≤′ (ℕP.≤-trans (ℕP.m≤n⊔m n₂ n₃) (ℕP.m≤n⊔m n₁ (n₂ ⊔ n₃)))
```

## 假后继树与两种分支

`fk y`: 把第 0 层的树 y 的每个后继换成第 1 层的常值结点. 严格值不变 (`fk-v`), 朝第 1 层折它只加不乘 (`fk-out`: 输出不高于底值 ⊕ y). `hon z` 是 `Ωt one` 的分支 z + 1; `wil z = fk (z + 1)` 与它同值.

```agda
module Wild (lem : LEM) where
  open Sharp lem
  open Term lem
  open NameP lem

  p₀ : Pos one
  p₀ = inj₂ (tt , inj₁ tt)

  β₁ : Tr⁺ one
  β₁ = Ωt one

  mutual
    fk : Tr zero → Tr one
    fk zero          = zero
    fk (suc y)       = Ω p₀ (λ _ → fk y)
    fk (lim g a)     = lim (λ n → fk (g n)) (λ n → fk-m (a n))
    fk (Ω () g)
    fk (up x () y e)

    fk-m : ∀ {x y : Tr zero} → zero ⊢ x ◃ y → one ⊢ fk x ◃ fk y
    fk-m ◃s       = ◃w
    fk-m (◃l n)   = ◃l n
    fk-m (◃t d e) = ◃t (fk-m d) (fk-m e)

  fk-v : (y : Tr zero) → ↑ one (fk y) ≈ᴸ ↑ zero y
  fk-v zero          = ≈ᴸ-refl zero
  fk-v (suc y)       = n≼ (λ _ → tt , proj₁ (fk-v y)) , n≼ (λ _ → zero , proj₂ (fk-v y))
  fk-v (lim g a)     = nd-cong (λ n → fk-v (g n))
  fk-v (Ω () g)
  fk-v (up x () y e)

  h₁ : Tr one → Tr one
  h₁ w = proj₁ (ψ♯ one o₁ B♯ one o₁ β₁ w)

  f₀ : Tr zero → Tr⁺ one
  f₀ y = ψ♯ zero tt B♯ one o₁ β₁ y

  f₀≽β : (y : Tr zero) → ↑ one (proj₁ β₁) ≼ᴸ ↑ one (proj₁ (f₀ y))
  f₀≽β zero          = ≼ᴸ-refl _
  f₀≽β (suc y)       = up≼ zero (f₀≽β y)
  f₀≽β (lim g a)     = up≼ zero (f₀≽β (g zero))
  f₀≽β (Ω () g)
  f₀≽β (up x () y e)

  next-mono : (b b′ : Tr⁺ one) → ↑ one (proj₁ b) ≼ᴸ ↑ one (proj₁ b′)
            → ↑ one (proj₁ (next⁺ b)) ≼ᴸ ↑ one (proj₁ (next⁺ b′))
  next-mono b b′ le = n≼ (λ n → n , it n)
    where
    it : ∀ n → ↑ one (iter (proj₁ b +_) (proj₁ b) n) ≼ᴸ ↑ one (iter (proj₁ b′ +_) (proj₁ b′) n)
    it zero    = le
    it (suc n) = ≼ᴸ-trans (proj₁ (↑-+ one (proj₁ b) (iter (proj₁ b +_) (proj₁ b) n)))
      (≼ᴸ-trans (≼ᴸ-trans (⊕-monoˡ le _) (⊕-monoʳ (↑ one (proj₁ b′)) (it n)))
                (proj₂ (↑-+ one (proj₁ b′) (iter (proj₁ b′ +_) (proj₁ b′) n))))

  f₀-mono : (x y : Tr zero) → ↑ zero x ≼ᴸ ↑ zero y → ↑ one (proj₁ (f₀ x)) ≼ᴸ ↑ one (proj₁ (f₀ y))
  f₀-mono zero y le = f₀≽β y
  f₀-mono (suc x) zero (n≼ h) = ⊥-elim (h tt)
  f₀-mono (suc x) (suc y) (n≼ h) = next-mono (f₀ x) (f₀ y) (f₀-mono x y (proj₂ (h tt)))
  f₀-mono (suc x) (lim g a) (n≼ h) = up≼ (suc (proj₁ (h tt)))
    (f₀-mono (suc x) (g (suc (proj₁ (h tt))))
      (n≼ (λ _ → ≼≺ (↑ zero (g (suc (proj₁ (h tt))))) (proj₂ (h tt)) (↑-strict zero (a (proj₁ (h tt)))))))
  f₀-mono (suc x) (Ω () g) le
  f₀-mono (suc x) (up _ () _ _) le
  f₀-mono (lim g a) y (n≼ h) = n≼ (λ n → ≺≼ (↑ one (proj₁ (f₀ (g (suc n))))) (↑ one (proj₁ (f₀ y)))
    (↑-strict one (mono♯ zero tt B♯ one o₁ β₁ (a n))) (f₀-mono (g (suc n)) y (≺→≼ (↑ zero y) (h (suc n)))))
  f₀-mono (Ω () g) y le
  f₀-mono (up _ () _ _) y le

  fk-out : (y : Tr zero) → ↑ one (h₁ (fk y)) ≼ᴸ ↑ one (proj₁ β₁) ⊕ ↑ zero y
  fk-out zero          = ≼ᴸ-refl _
  fk-out (suc y)       = n≼ (λ _ → tt , fk-out y)
  fk-out (lim g a)     = n≼ (λ n → n , fk-out (g n))
  fk-out (Ω () g)
  fk-out (up x () y e)

  hon wil : Tr zero → Tr one
  hon z = up zero tt (suc z) (z◃ z ◃s)
  wil z = Ω p₀ (λ _ → fk z)

  hon-v : ∀ z → ↑ one (hon z) ≈ᴸ nd sS (λ _ → ↑ zero z)
  hon-v z = nd-cong (λ _ → z⊕ (↑ zero z))

  wil-v : ∀ z → ↑ one (wil z) ≈ᴸ nd sS (λ _ → ↑ zero z)
  wil-v z = n≼ (λ _ → tt , proj₁ (fk-v z)) , n≼ (λ _ → zero , proj₂ (fk-v z))
```

## `xw` 名为 Ω₁

`xw` 的分支: 下标 z 有名字 (`Nd z`, 排中律判) 时取 `hon z`, 否则取 `wil z`. 命名关系的结点一行只问有名字的下标, 那里分支是 `hon z`, 名为 η + 1; 严格值逐分支与 `Ωt one` 相同. `nm-node` 对两棵树 (`xw` 与 `Ωt one`) 共用.

```agda
  Ω₁ᵗ : E.T
  Ω₁ᵗ = E.ψ (E.𝟏 ∷ []) [] ∷ []

  nf𝟏 : NF (E.𝟏 ∷ [])
  nf𝟏 = EB.nf-ψ EB.n[] EB.n[] EB.GB[]

  NdAt : Tr zero → E.T → Set
  NdAt z η = Σ (Acc _≺ᴸ_ zero) λ ac → Nmd zero tt ac z η

  Nd : Tr zero → Set
  Nd z = Σ E.T (NdAt z)

  pick : (z : Tr zero) → Nd z ⊎ (Nd z → ⊥) → Tr one
  pick z (inj₁ _) = hon z
  pick z (inj₂ _) = wil z

  xw : Tr one
  xw = Ω p₀ (λ z → pick z (lem (Nd z)))

  pick-v : ∀ z d → ↑ one (pick z d) ≈ᴸ nd sS (λ _ → ↑ zero z)
  pick-v z (inj₁ _) = hon-v z
  pick-v z (inj₂ _) = wil-v z

  nm-suc : ∀ {ac} (z : Tr zero) η → Nmd zero tt ac z η → Nmd zero tt ac (suc z) (E.sucT η)
  nm-suc {ac} z η (nη , vz , hz) =
    EBa.nf-sucT nη ,
    subst (λ m → nd sS (λ _ → ↑ zero z) ≈ᴸ sv m) (sym (⟦sucT⟧ η)) (nd-cong (λ _ → vz)) ,
    cof-sucT η , subst (Nmd zero tt ac z) (sym (pred-sucT η)) (nη , vz , hz)

  nm-hon : (r : ∀ {y} → y ≺ᴸ one → Acc _≺ᴸ_ y) (z : Tr zero) (η : E.T)
         → Nmd zero tt (r (tt , ≼ᴸ-refl zero)) z η → Nmd one o₁ (acc r) (hon z) (E.sucT η)
  nm-hon r z η nz =
    EBa.nf-sucT (proj₁ nz) ,
    ≈ᴸ-trans (hon-v z) (subst (λ m → nd sS (λ _ → ↑ zero z) ≈ᴸ sv m) (sym (⟦sucT⟧ η)) (nd-cong (λ _ → proj₁ (proj₂ nz)))) ,
    [] , E.sucT η , (EB.n[] , ≈ᴸ-refl zero , refl) , nm-suc z η nz , refl , ET.T-nil (E0.[]<sucT η)

  G-suc-inv : ∀ {u x} η → EB.InG u x (E.sucT η) → EB.InG u x η ⊎ (x ≡ [])
  G-suc-inv [] (EB.gp (EB.gh _))   = inj₂ refl
  G-suc-inv [] (EB.gp (EB.gw _ ()))
  G-suc-inv [] (EB.gp (EB.gc _ ()))
  G-suc-inv [] (EB.gtl ())
  G-suc-inv (y ∷ ys) (EB.gp i)  = inj₁ (EB.gp i)
  G-suc-inv (y ∷ ys) (EB.gtl i) with G-suc-inv ys i
  ... | inj₁ j = inj₁ (EB.gtl j)
  ... | inj₂ e = inj₂ e

  sw₁ : (η : E.T) → NF η → η E.<ᵀ E.Ωs [] → (E.fsT Ω₁ᵗ η ≤ᵀ E.sucT η) × ET.Trian η (E.sucT η) Ω₁ᵗ
  sw₁ η nη lt = inj₁ (E0.<-sucT η) , ET.mkT (EBa.suc<Ωs [] lt) (λ u c _ _ i → dm (G-suc-inv η i))
    where
    dm : ∀ {u c x} → EB.InG u x η ⊎ (x ≡ []) → ET.Dom u η c x
    dm (inj₁ j) = inj₂ (inj₂ (_ , j , inj₂ refl))
    dm (inj₂ e) = inj₂ (inj₁ e)

  nm-node : (g : Tr zero → Tr one) → ((z : Tr zero) → ↑ one (g z) ≈ᴸ nd sS (λ _ → ↑ zero z))
          → ((r : ∀ {y} → y ≺ᴸ one → Acc _≺ᴸ_ y) (z : Tr zero) (η : E.T)
               → Nmd zero tt (r (tt , ≼ᴸ-refl zero)) z η → Nmd one o₁ (acc r) (g z) (E.sucT η))
          → (ac : Acc _≺ᴸ_ one) → Nmd one o₁ ac (Ω p₀ g) Ω₁ᵗ
  nm-node g gv gn (acc r) =
    EB.nf-Ω nf𝟏 , nd-cong (λ c → ≈ᴸ-trans (gv c) (≈ᴸ-sym (hon-v c))) ,
    [] , refl , (≈ᴸ-refl zero , tt , refl) , E.sucT , gn r , sw₁

  pick-n : (r : ∀ {y} → y ≺ᴸ one → Acc _≺ᴸ_ y) (z : Tr zero) (η : E.T)
         → Nmd zero tt (r (tt , ≼ᴸ-refl zero)) z η → (d : Nd z ⊎ (Nd z → ⊥)) → Nmd one o₁ (acc r) (pick z d) (E.sucT η)
  pick-n r z η nz (inj₁ _)  = nm-hon r z η nz
  pick-n r z η nz (inj₂ no) = ⊥-elim (no (η , _ , nz))

  named-xw : (ac : Acc _≺ᴸ_ one) → Nmd one o₁ ac xw Ω₁ᵗ
  named-xw = nm-node (λ z → pick z (lem (Nd z))) (λ z → pick-v z (lem (Nd z))) (λ r z η nz → pick-n r z η nz (lem (Nd z)))

  named-β : (ac : Acc _≺ᴸ_ one) → Nmd one o₁ ac (proj₁ β₁) Ω₁ᵗ
  named-β = nm-node hon hon-v nm-hon
```

## B 的其余前提

目标层 `one` 名为 1; 底族在第 1 层上有名字 (层号的遗传命名把名字定成 1); ψ₁(Ω₁) 是标准形.

```agda
  lvn1 : (ac : Acc _≺ᴸ_ one) → LvN one o₁ ac (E.𝟏 ∷ [])
  lvn1 (acc r) = ≈ᴸ-refl one , tt , refl , refl

  ctx₁ : CtxN (λ i → i ≡ one) B♯ [] (E.𝟏 ∷ [])
  ctx₁ i oi (acc r) ι refl (_ , _ , c1e , pz) le =
    subst (λ t → Nmd one oi (acc r) (proj₁ β₁) (E.ψ t [] ∷ []))
          (trans (cong E.sucT (sym pz)) (E0.pred-suc ι c1e)) (named-β (acc r))

  tψ : E.T
  tψ = E.ψ (E.𝟏 ∷ []) Ω₁ᵗ ∷ []

  nfo : NF tψ
  nfo = EB.nf-ψ nf𝟏 (EB.nf-Ω nf𝟏) gb
    where
    gb : EB.GB (E.𝟏 ∷ []) Ω₁ᵗ Ω₁ᵗ
    gb (EB.gp (EB.gh _))                              = E.[]<
    gb (EB.gp (EB.gw _ (EB.gp (EB.gh (inj₁ ())))))
    gb (EB.gp (EB.gw _ (EB.gp (EB.gh (inj₂ ())))))
    gb (EB.gp (EB.gw _ (EB.gp (EB.gw _ ()))))
    gb (EB.gp (EB.gw _ (EB.gp (EB.gc _ ()))))
    gb (EB.gp (EB.gw _ (EB.gtl ())))
    gb (EB.gp (EB.gc _ ()))
    gb (EB.gtl ())
```

## 有名字的第 0 层的树有可数上界

`rp t`: 名为 t 的某棵第 0 层的树 (排中律取, 没有就取零). 同名的树由 (V) 同值, 所以 `rp t` 压住一切名为 t 的树. `c*` 是 `rp` 沿 `gen` 的部分和的极限.

```agda
  Rp : E.T → Set
  Rp t = Σ (Tr zero) λ z → NdAt z t

  rpd : (t : E.T) → Rp t ⊎ (Rp t → ⊥) → Tr zero
  rpd t (inj₁ w) = proj₁ w
  rpd t (inj₂ _) = zero

  rp : E.T → Tr zero
  rp t = rpd t (lem (Rp t))

  rp-ge : ∀ z t → NdAt z t → ↑ zero z ≼ᴸ ↑ zero (rp t)
  rp-ge z t n = go (lem (Rp t))
    where
    go : (d : Rp t ⊎ (Rp t → ⊥)) → ↑ zero z ≼ᴸ ↑ zero (rpd t d)
    go (inj₁ (z₀ , _ , n₀)) = ≼ᴸ-trans (proj₁ (proj₁ (proj₂ (proj₂ n)))) (proj₂ (proj₁ (proj₂ n₀)))
    go (inj₂ no)            = ⊥-elim (no (z , n))

  geR geL : (x y : Tr zero) → Set
  geR x y = ↑ zero y ≼ᴸ ↑ zero (x + suc y)
  geL x y = ↑ zero x ≼ᴸ ↑ zero (x + suc y)

  ger : ∀ x y → geR x y
  ger x y = up≼ tt (≼ᴸ-trans (≼⊕ʳ (↑ zero x) (↑ zero y)) (proj₂ (↑-+ zero x y)))

  gel : ∀ x y → geL x y
  gel x y = up≼ tt (≼ᴸ-trans (≼⊕ˡ (↑ zero x) (↑ zero y)) (proj₂ (↑-+ zero x y)))

  bl : List E.T → Tr zero
  bl []       = zero
  bl (t ∷ ts) = bl ts + suc (rp t)

  bl-ge : ∀ {t ts} → t ∈ ts → ↑ zero (rp t) ≼ᴸ ↑ zero (bl ts)
  bl-ge {ts = _ ∷ ts} (here refl) = ger (bl ts) _
  bl-ge {ts = s ∷ ts} (there i)   = ≼ᴸ-trans (bl-ge i) (gel (bl ts) (rp s))

  ee : ℕ → Tr zero
  ee zero    = suc (bl (gen zero))
  ee (suc n) = ee n + suc (bl (gen (suc n)))

  c* : Tr zero
  c* = lim ee (λ n → +-mono (ee n) (z◃ (bl (gen (suc n))) ◃s))

  ee-ge : ∀ n → ↑ zero (bl (gen n)) ≼ᴸ ↑ zero (ee n)
  ee-ge zero    = up≼ tt (≼ᴸ-refl _)
  ee-ge (suc n) = ger (ee n) _

  c*-ge : ∀ z η → NdAt z η → ↑ zero z ≼ᴸ ↑ zero c*
  c*-ge z η n = ≼ᴸ-trans (rp-ge z η n)
    (≼ᴸ-trans (bl-ge (proj₂ (cover η))) (up≼ (proj₁ (cover η)) (ee-ge (proj₁ (cover η)))))
```

## 保留支的输出与项模型不同值

朝第 1 层折 `xw` (默认底族, 底值 `Ωt one`, 上下文 0): 槽位层 (第 0 层) 严格低于目标层, 保留, 输出是结点, 分支 z′ 是折 `pick (τ z′)`. 项模型里 ψ₁(Ω₁) 的树是同一个折叠作用在 `Ωt one` 上, 分支 c 是折 `hon (τ c)`. 取 c = c* + 1: 有名字的下标的分支严格低于它 (`hon-lt`, 用 `c*-ge` 与 `f₀-mono`), 无名字的下标的分支低于底值的两倍 (`wil-lt`), 所以没有分支压住它.

```agda
  τ₀ : Tr zero → Tr zero
  τ₀ = τ zero zero tt tt (wfL zero) z≼

  τv : (ac : Acc _≺ᴸ_ zero) (le : zero ≼ᴸ zero) (x : Tr zero) → ↑ zero (τ zero zero tt tt ac le x) ≈ᴸ ↑ zero x
  τv ac le zero          = ≈ᴸ-refl zero
  τv ac le (suc x)       = nd-cong (λ _ → τv ac le x)
  τv ac le (lim f m)     = nd-cong (λ n → τv ac le (f n))
  τv ac le (Ω () g)
  τv ac le (up x () y e)

  hon-lt : ∀ (w c : Tr zero) → ↑ zero w ≼ᴸ ↑ zero c → ↑ one (h₁ (hon w)) ≺ᴸ ↑ one (h₁ (hon (suc c)))
  hon-lt w c le = ≼≺ (↑ one (h₁ (hon (suc c)))) (next-mono (f₀ w) (f₀ c) (f₀-mono w c le)) (zero , ≼ᴸ-refl _)

  wil-lt : ∀ (w c : Tr zero) → ↑ one (h₁ (wil w)) ≺ᴸ ↑ one (h₁ (hon c))
  wil-lt w c = ≺≼ (↑ one (proj₁ (next⁺ β₁))) (↑ one (h₁ (hon c)))
    (≼≺ (↑ one (proj₁ (next⁺ β₁))) (fk-out (suc w))
        (suc zero , ≼ᴸ-trans (≺→≼ (↑ one (proj₁ β₁) ⊕ ↑ one (proj₁ β₁))
                                (⊕-strictʳ (↑ one (proj₁ β₁)) (↑ one (proj₁ β₁)) (tb↑ zero (suc w))))
                             (proj₂ (↑-+ one (proj₁ β₁) (proj₁ β₁)))))
    (next-mono β₁ (f₀ c) (f₀≽β c))

  outw outm : Tr⁺ one
  outw = ψ♯ one o₁ B♯ one o₁ β₁ xw
  outm = ψ♯ one o₁ B♯ one o₁ β₁ (proj₁ β₁)

  model≡ : sv ⟦ tψ ⟧ ≡ ↑ one (proj₁ outm)
  model≡ = refl

  ≼-inv : ∀ {s h b} → nd s h ≼ᴸ b → (c : Ch s) → h c ≺ᴸ b
  ≼-inv (n≼ f) = f

  final : ∀ z′ (d : Nd (τ₀ z′) ⊎ (Nd (τ₀ z′) → ⊥))
        → ↑ one (h₁ (hon (suc (τ₀ c*)))) ≼ᴸ ↑ one (h₁ (pick (τ₀ z′) d)) → ⊥
  final z′ (inj₁ (η , n)) le = ≺-irrefl (↑ one (h₁ (hon (suc (τ₀ c*)))))
    (≼≺ (↑ one (h₁ (hon (suc (τ₀ c*))))) le
        (hon-lt (τ₀ z′) (τ₀ c*) (≼ᴸ-trans (c*-ge (τ₀ z′) η n) (proj₂ (τv (wfL zero) z≼ c*)))))
  final z′ (inj₂ _) le = ≺-irrefl (↑ one (h₁ (hon (suc (τ₀ c*)))))
    (≼≺ (↑ one (h₁ (hon (suc (τ₀ c*))))) le (wil-lt (τ₀ z′) (suc (τ₀ c*))))

  ¬same-value : ↑ one (proj₁ outm) ≼ᴸ ↑ one (proj₁ outw) → ⊥
  ¬same-value me = final (proj₁ (≼-inv me (suc c*))) (lem (Nd (τ₀ (proj₁ (≼-inv me (suc c*)))))) (proj₂ (≼-inv me (suc c*)))

  B-keep-false : (D : L → Set) → CtxN D B♯ [] (E.𝟏 ∷ []) → BRow D one o₁ xw → ⊥
  B-keep-false D cx b = ¬same-value (proj₂ (proj₁ (proj₂
    (b (wfL one) B♯ one o₁ (wfL one) β₁ Ω₁ᵗ (E.𝟏 ∷ []) [] tt (named-xw (wfL one)) (lvn1 (wfL one)) cx (named-β (wfL one)) nfo))))

  B-keep-false₁ : BRow (λ i → i ≡ one) one o₁ xw → ⊥
  B-keep-false₁ = B-keep-false (λ i → i ≡ one) ctx₁
```
