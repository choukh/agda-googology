# TreeLevels O8：`nκ` 展开后一段的非空上下文模拟

`RunK` 展开 `nκ` 后，`κΔ` 调用 `Walk`；`Walk` 的后继行调用 `Run`
走 ũ c = ni self (λ _ → n1)。因此不能仅以旧 `Rl` 无 `nκ` 规则
停止：这一段可以先展开到旧模拟器支持的节点。本篇实际检验其在
非空前缀 `X` 下的一步，保留原 `Run`、原 `A₁` 与原状态不变量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO8Cell where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans; refl)
open import OCF.Align.CumReadCF hiding (rkT; keep; rise; Rk) renaming (_⊕_ to _+ᵒ_)
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (add-mono; ψL; Ω⊴)
open import OCF.Align.TLRuleRel using (add-ContF; ≈-rp; emb; emb≈; emb≈ˡ; emb≈ʳ; emb⊴ˡ; emb⊴ʳ)
open import OCF.Align.SumOneTree using (D̂; Dl; Ly; top; ni; n0; n1; tailP)
open import OCF.Align.SumOneRel
open import OCF.Align.SumOneSim
open import OCF.Align.SumOneClosed
open import OCF.Align.SumOneTop using (seg-T; I₁; ũ; zero-Inv; i₁)
```

先把已有 `add-Rel` 从可数目标片段推广到 `Rl`。这里只改变关系的端点，
不改变差树，不要求输入含有新的构造子。

```agda
add-Rl : ∀ {ly M W} (B : O M) → B ≈ B → ∀ {b x y} →
  Rl ly M {W} b x y → Rl ly M (B +ᵒ b) x (B +ᵒ y)
add-Rl B e {b} {y = y} (rz d p) = rz (add≈ self self e b y d) (add≈ self self e y y p)
add-Rl B e {b} {y = y} (rs d p) = rs (add≈ self self e y (os b) d) (add≈ self self e y y p)
add-Rl B e (rc D₁ D₂) = rc (add-Rl B e D₁) (add-Rl B e D₂)
add-Rl B e {b} (rb {b = b₁} d p D) = rb (add≈ self self e b b₁ d) (add≈ self self e b₁ b₁ p) (add-Rl B e D)
add-Rl B e {y = y′} (rr {y = y} D d p) = rr (add-Rl B e D) (add≈ self self e y y′ d) (add≈ self self e y′ y′ p)
add-Rl B e (rw D) = rw (add-Rl B e D)
add-Rl B e {b} {y = y} (rl g d p q e₀ steps) =
  rl (λ n → B +ᵒ g n) (add≈ self self e y (ol g) d) (add≈ self self e y y p) (λ n → add≈ self self e (g n) (g n) (q n))
     (add≈ self self e b (g 0) e₀) (λ m → add-Rl B e (steps m))
add-Rl B e {y = y} (rd g d p q f D) =
  rd (λ n → B +ᵒ g n) (add≈ self self e y (ol g) d) (add≈ self self e y y p) (λ n → add≈ self self e (g n) (g n) (q n))
     (add-mono self self e f) (add-Rl B e D)
add-Rl B e {b} {y = y} (ri {k = k} r u p₀ H d p e₀ C ds) =
  ri r u p₀ (λ z → B +ᵒ H z)
     (≈-rp (B +ᵒ y) {r = p₀} (add≈ self self e y (oi p₀ (λ z → H (outS (≪S p₀) z))) d)
        (λ a → cong (λ v → B +ᵒ H v) (trans (out-inS (≪S p₀) _) (out-inS (≪S p₀) a))))
     (add≈ self self e y y p)
     (add≈ self self e b (H (Ω̇ k)) e₀)
     (add-ContF B e C)
     (λ q lW′ w z₀ z₁ c d′ p′ → add-Rl B e (ds q lW′ w z₀ z₁ c d′ p′))

segment-in-context : ∀ {c V} (p : asuc c ⊲ V) (lV : Lg V)
  (X : O V) → X ≈ X → (co : D̂ V) (Y : St V) →
  Inv Y (X +ᵒ emb (⊲-tr (suc self) p) (Ω̇ c)) →
  Diff (Run accTop (ni {k = c} self (λ _ _ _ → n1))
      (⊲-tr (suc self) p) lV tt A₁ co Y)
    (X +ᵒ emb (⊲-tr (suc self) p) (Ω̇ c))
    (X +ᵒ emb p (Ω̇ (asuc c)))
segment-in-context {c} p lV X eX co Y inv =
  RS accTop q lV tt I₁ (add≈ self self eX b b (emb≈ q q (Ω≈ c)))
    (add-Rl X eX (seg-T p)) Y inv
  where
  q = ⊲-tr (suc self) p
  b = emb q (Ω̇ c)
```

该结论仍消费准确的 `Inv`，不是只消费第 0 层输出的值不等式。
所以它不能直接把候选自身的世界序列与参照的 γ 序列按值对齐；
这一部分尚需继续实填。

## 包含极限世界的整段

下面沿原 `Walk` / `WRp` 互递归，扩展到一整格 `κΔ`。前缀 `X`
是同一实际世界中的旧树，全部层号比较沿现有共同界路径进行。
没有添加任意值序下的单调假设。

```agda
module Context {V₁ : A} (X : O V₁) (eX : X ≈ X) where
  ctx : ∀ {a} → a ⊲ V₁ → O a → O V₁
  ctx q b = X +ᵒ emb q b

  ctx≈ : ∀ {a b} (p : a ⊲ V₁) (q : b ⊲ V₁) {x : O a} {y : O b} → x ≈ y → ctx p x ≈ ctx q y
  ctx≈ p q e = add≈ self self eX _ _ (emb≈ p q e)

  walk : ∀ b {a W₀} (p : a ⊲ b) (ap : W₀ ⊲ a) (lb : Lg b)
    (bV : b ⊲ V₁) (q : a ⊲ V₁) (lV : Lg V₁) (co : D̂ V₁) (Y : St V₁) →
    Inv Y (ctx q (Ω̇ a)) →
    Diff (Walk accTop ũ b p ap lb bV lV tt A₁ co Y) (ctx q (Ω̇ a)) (ctx bV (Ω̇ b))
  rpt : ∀ {a W₀ n} (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n))
    (wl : ∀ n → Lg (f n)) (p : a ⊲ f n) (ap : W₀ ⊲ a)
    (fV : ∀ m → f m ⊲ V₁) (lV : Lg V₁) (co : D̂ V₁) (Y : St V₁) →
    Inv Y (ctx (fV n) (Ω̇ (f n))) → ∀ m →
    Inv (proj₂ (WRp accTop ũ f stp wl p ap fV lV tt A₁ co Y m)) (ctx (fV (m + n)) (Ω̇ (f (m + n))))

  walk b self ap lb bV q lV co Y v τ lt T l T′ l′ =
    rz (ψQ _ _ T l T′ l′ (ctx≈ q bV (Ω≈ b)))
      (ψQ _ _ T′ l′ T′ l′ (ctx≈ bV bV (Ω≈ b)))
  walk (asuc c) (suc p) ap lb bV q lV co Y v τ lt T l T′ l′ =
    rc (walk c p ap lb cV q lV co Y v τ lt T l T′ l′)
      (segment-in-context bV lV X eX _ (Y ⊕ Walk accTop ũ c p ap lb cV lV tt A₁ co Y)
        (inv+ v (walk c p ap lb cV q lV co Y v)) τ lt T′ l′ T′ l′)
    where
    cV = ⊲-tr (suc self) bV
  walk (alim f) (lim n p) ap (stp , wl) bV q lV co Y v τ lt T l T′ l′ =
    rc (walk (f n) p ap (wl n) (fV n) q lV co Y v τ lt T l T′ l′)
      (drpn n Gt
        (ψQ _ _ T′ l′ T′ l′ (add≈ self self eX
          (emb bV (Ω̇ (alim f))) (ol (λ m → emb (fV m) (Ω̇ (f m))))
          (emb≈ˡ bV {x = Ω̇ (alim f)} {y = ol (λ m → emb (fV m) (Ω̇ (f m)))}
            (λ m → emb≈ʳ (fV m) (Ω≈ (f m))))))
        (ψQ _ _ T′ l′ T′ l′ (ctx≈ bV bV (Ω≈ (alim f))))
        (λ i → ψQ _ _ T′ l′ T′ l′ (ctx≈ (fV i) (fV i) (Ω≈ (f i))))
        (λ i → ψL T′ l′ T′ l′ (add-mono self self eX
          (emb⊴ˡ (fV i) (emb⊴ʳ (fV (suc i)) (Ω⊴ (stp i))))))
        (ψQ _ _ T′ l′ T′ l′ (ctx≈ (fV n) (fV n) (Ω≈ (f n))))
        (λ m → walk (f (suc (m + n))) (stp (m + n))
          (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n)))
          (fV (suc (m + n))) (fV (m + n)) lV _ _
          (rpt f stp wl p ap fV lV _ _
            (inv+ v (walk (f n) p ap (wl n) (fV n) q lV co Y v)) m)
          τ lt T′ l′ T′ l′))
    where
    fV : ∀ m → f m ⊲ V₁
    fV m = ⊲-tr (lim m self) bV
    Gt : ℕ → O _
    Gt m = ψ _ T′ l′ (ctx (fV m) (Ω̇ (f m)))

  rpt f stp wl p ap fV lV co Y v zero = v
  rpt {n = n} f stp wl p ap fV lV co Y v (suc m) =
    inv+ (rpt f stp wl p ap fV lV co Y v m)
      (walk (f (suc (m + n))) (stp (m + n))
        (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n)))
        (fV (suc (m + n))) (fV (m + n)) lV _ _
        (rpt f stp wl p ap fV lV co Y v m))

cell-in-context : (c : Cl one azero top) (X : O (v c)) → X ≈ X →
  Inv (Sv c) (X +ᵒ emb (av c) (Ω̇ (a c))) →
  Diff (κΔ accTop ũ tt A₁ c) (X +ᵒ emb (av c) (Ω̇ (a c))) (X +ᵒ Ω̇ (v c))
cell-in-context c X eX inv = Context.walk X eX (v c) (av c) (ap c)
  (lv c) self (av c) (lv c) (co c) (Sv c) inv
```

`segment-in-context` 的非空前缀前提确有实例：下例前缀为 1，原 `Step`
执行两次得到所需状态。它只检查条件可满足，不是所求上界或新强度。

```agda
two-steps : St one
two-steps = (Y₀ ⊕ Step Y₀) ⊕ Step (Y₀ ⊕ Step Y₀)

two-steps-inv : Inv {one} two-steps (os (os o0))
two-steps-inv = inv+ v₁ (i₁ (Y₀ ⊕ Step Y₀) (os o0) (os (os o0)) tt tt tt v₁)
  where
  v₀ : Inv {one} Y₀ o0
  v₀ = zero-Inv Y₀ (λ τ lt → refl)
  v₁ : Inv {one} (Y₀ ⊕ Step Y₀) (os o0)
  v₁ = inv+ v₀ (i₁ Y₀ o0 (os o0) tt tt tt v₀)

nonempty-segment : Diff (Run accTop (ni {k = azero} self (λ _ _ _ → n1))
  (suc self) tt tt A₁ n0 two-steps)
  (os o0 +ᵒ emb (suc self) (Ω̇ azero)) (os o0 +ᵒ Ω̇ one)
nonempty-segment = segment-in-context self tt (os o0) tt n0 two-steps two-steps-inv

example-cell : Cl one azero top
example-cell = mkCl one tt self azero self (suc self) two-steps n0

nonempty-cell : Diff (κΔ accTop ũ tt A₁ example-cell)
  (os o0 +ᵒ emb (suc self) (Ω̇ azero)) (os o0 +ᵒ Ω̇ one)
nonempty-cell = cell-in-context example-cell (os o0) tt two-steps-inv
```

`example-cell` 是手工填入合法世界与路径的具体 `Cl`，认证整格定理的
准确 `Inv` 前提可满足；它没有被认作原 `Cℓ` 序列或原完整 `Y₁`。
