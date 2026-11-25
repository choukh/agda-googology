# 作用域块上的一致性: 嵌入支里的折叠就是孩子里的折叠

非验收文件. 判决: 编译定理, 都是 `refl`, 无前提, 对一切种类的层号 (`one`, `nat`, `raw k`) 与一切孩子下标成立. 孩子的下标只是被传过去, 没有被检查.
`top` 的各行是结点行与 `into` 行的推论 (`top-zero`, `top-one`, `top-nat`, `top-raw`). 不说明合法性与值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeSame where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiScopeCore
open import OCF.Lean.YiScopeFold
```

## 1 加法不摊平; 嵌入支的折叠

```agda
plus-into : ∀ {X} S g (x : Tr X (sup S g) root) (c : Ar S) (t : Tr ⊥ (sup S g) (down c root)) →
  plus {s = root} x (G.into c t) ≡ G.into c (plus x t)
plus-into S g x c t = refl

-- 左加数原样到达孩子里那棵树的底: 越出孩子的 up 下面.
plus-up : ∀ {X} S g (x : Tr X (sup S g) root) c y →
  plus x (G.up {s = root} {s′ = down c root} c refl y) ≡ G.up {s = root} c refl (plus x y)
plus-up S g x c y = refl

F-into : ∀ {X} (ρ : X → Res) S g J b c t →
  F ρ (sup S g) J col b (G.into c t) ≡ F (λ v → v) (g c) J col b (dn ρ (sup S g) (down c root) t)
F-into ρ S g J b c t = refl

F-plus-into : ∀ (ρ : ⊥ → Res) S g J b x (c : Ar S) (t : Tr ⊥ (sup S g) (down c root)) →
  F ρ (sup S g) J col b (plus {s = root} x (G.into c t)) ≡
  F (λ v → v) (g c) J col b (dn ρ (sup S g) (down c root) (plus x t))
F-plus-into ρ S g J b x c t = refl

-- 越出孩子的东西在孩子里是一个洞, 洞里是外面那棵树对任意目标层的折叠.
dn-up : ∀ {X} (ρ : X → Res) S g c y →
  dn ρ (sup S g) (down c root) (G.up {s = root} c refl y) ≡ G.hole (λ J b → F ρ (sup S g) J col b y)
dn-up ρ S g c y = refl

```

## 2 孩子根上的结点: 链在孩子那一层按孩子自己的规则算

```agda
node-in-child : ∀ {X} (ρ : X → Res) S g J b c r h →
  F ρ (sup S g) J col b (G.into c (G.nd r h)) ≡
  G.lim (λ n → F (λ v → v) (g c) J col b (dn ρ (sup S g) (down c root)
    (h (chainD (g c) r (λ γ → RlD (λ v → v) (g c) r (tpD (g c) root r) (dn ρ (sup S g) (down c root) (h γ))) n))))
node-in-child ρ S g J b c r h = refl

-- 后继层的根结点的链步: 孩子里的东西原样保留 (结点, into), 越过孩子根的 up 回到 F.
kp-into : ∀ {X} (ρ : X → Res) g b t →
  F ρ (sup one g) (g tt) kp b (G.into tt t) ≡ In ρ (sup one g) (down tt root) b t
kp-into ρ g b t = refl

In-nd : ∀ {X} (ρ : X → Res) g p b r h →
  In ρ (sup one g) (down tt p) b (G.nd r h) ≡ G.nd r (λ η → In ρ (sup one g) (down tt p) b (h η))
In-nd ρ g p b r h = refl

In-into : ∀ {X} (ρ : X → Res) g p b d t →
  In ρ (sup one g) (down tt p) b (G.into d t) ≡ G.into d (In ρ (sup one g) (down tt (sub (g tt) p d)) b t)
In-into ρ g p b d t = refl

In-esc : ∀ {X} (ρ : X → Res) g b y →
  In ρ (sup one g) (down tt root) b (G.up {s = root} tt refl y) ≡ F ρ (sup one g) (g tt) kp b y
In-esc ρ g b y = refl

-- 同一个结点放在任意层号的任意孩子 c 的孩子里 (c 是变量): 保留, 输出与 c 无关.
keep-any : ∀ S (c : Ar S) (a : Level) (b : Raw (sucᴸ a)) →
  F {X = Res} (λ v → v) (sucᴸ (sucᴸ a)) (sucᴸ a) kp b
    (dn ⊥-elim (sup S (λ _ → sucᴸ (sucᴸ a))) (down c root) (G.into tt (G.nd tt (λ _ → G.zero))))
  ≡ G.nd tt (λ _ → b)
keep-any S c a b = refl
```

## 3 `top` 的各行

```agda
top-zero : ∀ (ρ : ⊥ → Res) J b x → F ρ zero J col b (top zero x) ≡ succ (F ρ zero J col b x)
top-zero ρ J b x = refl

top-one : ∀ (ρ : ⊥ → Res) g J b x →
  F ρ (sup one g) J col b (top (sup one g) x) ≡
  G.lim (λ n → F ρ (sup one g) J col b (plus {s = root} x (G.into tt (un one g tt ⊥-elim root
    (chain (g tt) (λ γ → F ρ (sup one g) (g tt) kp (top (g tt) G.zero)
      (plus {s = root} x (G.into tt (un one g tt ⊥-elim root γ)))) n)))))
top-one ρ g J b x = refl

top-nat : ∀ (ρ : ⊥ → Res) g J b x →
  F ρ (sup nat g) J col b (top (sup nat g) x) ≡
  G.lim (λ n → F ρ (sup nat g) J col b (acc (λ m z → ct nat g (suc m) z) (ct nat g 0 x) n))
top-nat ρ g J b x = refl

top-raw : ∀ (ρ : ⊥ → Res) k g J b x →
  F ρ (sup (raw k) g) J col b (top (sup (raw k) g) x) ≡
  G.lim (λ n → F ρ (sup (raw k) g) J col b (Kf k (ct (raw k) g) x
    (chain k (λ γ → F ρ (sup (raw k) g) k col (top k G.zero) (Kf k (ct (raw k) g) x γ)) n)))
top-raw ρ k g J b x = refl
```
