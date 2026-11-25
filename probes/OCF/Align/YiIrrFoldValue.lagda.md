# YiIrrFold 第 4 层：折叠在规范实例上的序数值

**验收文件。** 允许导入带记号闭包的 `Value`、`RR4ChainAdd`、`RR4MonoFragment` 与旧验收 `YiK2cValue`
(只取它参照树一侧的定义与定理)；定义与证书文件 (`YiIrrFoldBase`, `YiIrrFold`, `YiIrrFoldInst`,
`YiIrrFoldSeed`) 不导入本篇，也不读 `Value` 的序。没有 Funext。

验收的是 [YiIrrFold](YiIrrFold.lagda.md) 的同一个递归折叠 `ψ` 在三族输入上的输出，读成 `Level` 的可数树后与参照比较。
三行都是序数值验收 (互相 `≼`)，不是基本列验收：

| 输入 | 定理 | 陈述 |
|---|---|---|
| 规范 Ω₁ (`tw 2`) | `same-on-Ω₁` | `read (ψ (tw 2)) ≈ᵛ ψ⁰ Ω₁` |
| Ω₁·(n+1) (`sum n`)，一切 n | `finite-same` | `read (ψ (sum n)) ≈ᵛ ψ⁰ (reference n)` |
| lim Ω₁·(n+1) (`limit`) | `omega-same` | `read (ψ limit) ≈ᵛ ψ⁰ (lim reference)` |

中间的 `Lower.append-lower` 与 `Upper.append-upper` 是对结构参数的一步定理：对任何 `Dom` 里的前缀 `x`
与带结构自模拟的参照 `X`，若 `ψ⁰ X ≼ read (ψ x)`，则 `ψ⁰ (X + Ω₁) ≼ read (ψ (x + Ω₁))`；反向同理。
这一步新用到的只有前缀的自模拟与折叠的四行，没有按阶段加前提。证明照 [YiK2Value](YiK2Value.lagda.md)、
[YiK2cValue](YiK2cValue.lagda.md) 与 [RR4ChainAdd](RR4ChainAdd.lagda.md) §3；
区别是那里被验收的是为每个族单独写的 `tail`，并且嵌套的两族只有下界，这里被验收的是 `ψ` 自己，两个方向都有。

没有的：`Dom` 里其它树的值 (包括 Ω₁²)；从层号树到 `Level` 第 1 层的一般解释；基本列一致；FGH 的比较。
强度没有变化：这些值都在 ψ₀(Ω₁·ω) 以内，值前沿仍是 ψ₀(Ω_{Ω·ω²})。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFoldValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G)
open import OCF.Align.RR5IrrCheck using (tw)
open import OCF.Align.YiIrrIf
  using (R; one; _+ʳ_; copies; successor; read0; Point; point; coordinate;
         start; iterate; module FoldRows)
open import OCF.Align.YiIrrFoldBase using (Dom; dom-at; dom-branch; dom-Ω₁)
open import OCF.Align.YiIrrFold using (ψ; fold-rows)
open import OCF.Align.YiIrrFoldInst
  using (_+ᴸ_; add-dom; sum; sum-dom; limit; limit-dom)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4ChainAdd as A
import OCF.Align.RR4MonoFragment as M
import OCF.Align.YiK2cValue as K
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open L using (_≅_; z≅; s≅; l≅; ≅-refl⁰; ≅-trans; add-≅)
open V using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≅→≈ᵛ; +-mono; ψ⁰-mono⁰; l≼; ≼l;
              ≼i; i≼; ≼u; u≼; z≼; s≼s)

module F = FoldRows fold-rows
```

## 1 第 0 层的值读成可数树

`read` 与旧块上的 `YiK2Value.read` 逐行相同，只换了块。`top` 读作 1。

```agda
read : R → L.Ordᶜ L.zero
read G.zero = L.zero
read (G.suc x) = L.suc (read x)
read (G.lim f) = L.lim (λ n → read (f n))
read (G.lc () c t g)
read (G.em () t)
read G.top = L.suc L.zero

read-add : ∀ x y → read (x +ʳ y) ≅ (read x L.+ read y)
read-add x G.zero = ≅-refl⁰ (read x)
read-add x (G.suc y) = s≅ (read-add x y)
read-add x (G.lim f) = l≅ (λ n → read-add x (f n))
read-add x (G.lc () c t g)
read-add x (G.em () t)
read-add x G.top = s≅ (≅-refl⁰ (read x))

read-copies : ∀ x (y : L.Ordᶜ L.zero) → read x ≅ y → ∀ n →
  read (copies x n) ≅ iter (y L.+_) L.zero n
read-copies x y e zero = z≅
read-copies x y e (suc n) =
  ≅-trans (read-add x (copies x n))
    (add-≅ {σ = λ q → q} {σ′ = λ q → q} e (read-copies x y e n))

read-add-≈ : ∀ x y → read (x +ʳ y) ≈ᵛ (read x L.+ read y)
read-add-≈ x y = ≅→≈ᵛ (read-add x y)
```

## 2 折叠在读回上：与 `ψ⁰` 逐结构互模拟

`ψ` 在 `read0 a` 上只走零、后继、极限三行。证书参数是无关的，所以这条对任何证书陈述。

```agda
read-fold : ∀ a .(d : Dom (read0 a)) → read (ψ (read0 a) d) ≅ L.ψ⁰ (read a)
read-fold G.zero d = s≅ z≅
read-fold (G.suc a) d =
  l≅ (read-copies (ψ (read0 a) d) (L.ψ⁰ (read a)) (read-fold a d))
read-fold (G.lim f) d =
  l≅ (λ n → read-fold (f n) (dom-at (λ n → read0 (f n)) d n))
read-fold (G.lc () c t g) d
read-fold (G.em () t) d
read-fold G.top d = l≅ (read-copies one (L.suc L.zero) (s≅ z≅))
```

## 3 规范 Ω₁：同值

`pts` 是 `ψ (tw 2)` 的 gt 行里那条链 (接口的 `next` 与 `start`)，`rchain` 是它的坐标。
逐项与 `RR4ChainAdd` 的加法链 `chain⁺ idᵇ` 按值比较，再用那里的 `same-on-Ω₁`。

```agda
Ω₁-next : Point one → Point one
Ω₁-next = F.next one tt tt (B.suc B.zero) (λ η e → read0 η) dom-Ω₁

Ω₁-out : Point one → R
Ω₁-out = F.out one tt tt (B.suc B.zero) (λ η e → read0 η) dom-Ω₁

pts : ℕ → Point one
pts = iterate Ω₁-next (start one tt tt)

rchain : ℕ → R
rchain n = coordinate (pts n)

out-fold : ∀ (p : Point one) → read (Ω₁-out p) ≈ᵛ L.ψ⁰ (read (coordinate p))
out-fold (point η e) = ≅→≈ᵛ (read-fold η
  (dom-branch one tt tt (B.suc B.zero) (λ η e → read0 η) dom-Ω₁ η e))

chain-forward : ∀ n → read (rchain n) ≼ A.chain⁺ A.idᵇ n
chain-forward zero = ≼-refl (L.suc L.zero)
chain-forward (suc n) =
  ≼-trans (proj₁ (read-add-≈ (rchain n) (Ω₁-out (pts n))))
    (+-mono (chain-forward n)
      (≼-trans (proj₁ (out-fold (pts n)))
        (≼-trans (ψ⁰-mono⁰ (chain-forward n))
          (M.step≽ A.idᵇ (A.chain⁺ A.idᵇ n)))))

chain-backward : ∀ n → A.chain⁺ A.idᵇ n ≼ read (rchain n)
chain-backward zero = ≼-refl (L.suc L.zero)
chain-backward (suc n) =
  ≼-trans
    (+-mono (chain-backward n)
      (≼-trans (M.step≼ A.idᵇ (A.chain⁺ A.idᵇ n))
        (≼-trans (ψ⁰-mono⁰ (chain-backward n))
          (proj₂ (out-fold (pts n))))))
    (proj₂ (read-add-≈ (rchain n) (Ω₁-out (pts n))))

fold-additive : read (ψ (tw 2) dom-Ω₁) ≈ᵛ A.F⁺ A.idᵇ
fold-additive =
  l≼ (λ n → ≼l n (≼-trans (proj₁ (out-fold (pts n)))
    (ψ⁰-mono⁰ (chain-forward n)))) ,
  l≼ (λ n → ≼l n (≼-trans (ψ⁰-mono⁰ (chain-backward n))
    (proj₂ (out-fold (pts n)))))

same-on-Ω₁ : read (ψ (tw 2) dom-Ω₁) ≈ᵛ L.ψ⁰ V.Ω₁
same-on-Ω₁ =
  ≼-trans (proj₁ fold-additive) (proj₁ A.same-on-Ω₁) ,
  ≼-trans (proj₂ A.same-on-Ω₁) (proj₂ fold-additive)
```

## 4 一步定理：前缀再加一个 Ω₁

`X` 是第 1 层的参照前缀，`ex` 是它的结构自模拟；`x` 是 `Dom` 里的层号树。
参照一侧 (`Ref`) 只依赖 `X`：`H y = ψ⁰ (X + y)`，参照的链 `original` 每步是 `H` (差一个结构互模拟)。
`H`, `H-mono`, `step≤H` 照 `YiK2cValue.Bound`；`y≼H`, `suc-H`, `dbl-H`, `o-strict` 是
`RR4ChainAdd` §3 里 `x≼ψ⁰`, `suc-ψ⁰`, `dbl-ψ⁰`, `c-strict` 把 `ψ⁰` 换成 `H` 的同一组证明。

```agda
raw-suc-lower : ∀ a {x : L.Ordᶜ (L.suc L.zero)} →
  L.ψ⁰ x ≼ read a → L.ψ⁰ (L.suc x) ≼ read (successor a)
raw-suc-lower a low = l≼ (λ n → ≼l n
  (≼-trans (V.iter-≼ low n)
    (proj₂ (≅→≈ᵛ (read-copies a (read a) (≅-refl⁰ (read a)) n)))))

raw-suc-upper : ∀ a {x : L.Ordᶜ (L.suc L.zero)} →
  read a ≼ L.ψ⁰ x → read (successor a) ≼ L.ψ⁰ (L.suc x)
raw-suc-upper a high = l≼ (λ n → ≼l n
  (≼-trans (proj₁ (≅→≈ᵛ (read-copies a (read a) (≅-refl⁰ (read a)) n)))
    (V.iter-≼ high n)))

module Ref (X : L.Ordᶜ (L.suc L.zero)) (ex : X L.≅ X) where

  prefix : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
  prefix y = L.add X (λ q → L.suc q) y

  H : L.Ordᶜ L.zero → L.Ordᶜ L.zero
  H y = L.ψ⁰ (prefix y)

  base≤H : ∀ y → H L.zero ≼ H y
  base≤H L.zero = ≼-refl (H L.zero)
  base≤H (L.suc y) = ≼l 1 (base≤H y)
  base≤H (L.lim f) = ≼l 0 (base≤H (f 0))
  base≤H (L.limᵢ () f)
  base≤H (L.up () y)

  H-mono : ∀ {y z} → y ≼ z → H y ≼ H z
  H-mono {z = z} z≼ = base≤H z
  H-mono (s≼s p) = V.ψ⁰-suc-≼ (H-mono p)
  H-mono (≼l n p) = ≼l n (H-mono p)
  H-mono (l≼ h) = l≼ (λ n → H-mono (h n))
  H-mono (≼i {p = ()} y e p)
  H-mono (i≼ {p = ()} h)
  H-mono (≼u {r = ()} p)
  H-mono (u≼ {r = ()} p)

  step : L.Ordᶜ L.zero → L.Ordᶜ L.zero
  step y = L.ψ L.zero (λ q → q) (prefix y)

  original : ℕ → L.Ordᶜ L.zero
  original = iter step (L.suc L.zero)

  reference-row : L.ψ⁰ (X L.+ V.Ω₁) ≡ L.lim (λ n → H (original n))
  reference-row = refl

  prefix-self : ∀ y → prefix y L.≅ prefix y
  prefix-self y = add-≅ {σ = λ q → L.suc q} {σ′ = λ q → L.suc q}
    ex (≅-refl⁰ y)

  step≈H : ∀ y → H y ≈ᵛ step y
  step≈H y = ≅→≈ᵛ (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → q} (prefix-self y))

  step≤H : ∀ y → step y ≼ H y
  step≤H y = proj₂ (step≈H y)

  step≥H : ∀ y → H y ≼ step y
  step≥H y = proj₁ (step≈H y)

  1≼H : ∀ y → L.suc L.zero ≼ H y
  1≼H y = V.1≼ψ⁰ (prefix y)

  y≼H : ∀ y → y ≼ H y
  y≼H L.zero = z≼
  y≼H (L.suc y) = ≼l 2 (+-mono (y≼H y) (1≼H y))
  y≼H (L.lim f) = l≼ (λ n → ≼l n (y≼H (f n)))
  y≼H (L.limᵢ () f)
  y≼H (L.up () y)

  suc-H : ∀ y → L.suc (H y) ≼ H (L.suc y)
  suc-H y = ≼l 2 (+-mono (≼-refl (H y)) (1≼H y))

  dbl-H : ∀ y → (y L.+ H y) ≼ H (L.suc y)
  dbl-H y = ≼l 2 (+-mono (y≼H y) (≼-refl (H y)))

  o-strict : ∀ n → L.suc (original n) ≼ original (suc n)
  o-strict zero =
    ≼-trans (≼l 2 (+-mono (1≼H L.zero) (1≼H L.zero))) (step≥H (L.suc L.zero))
  o-strict (suc n) =
    ≼-trans (s≼s (step≤H (original n)))
    (≼-trans (suc-H (original n))
    (≼-trans (H-mono (o-strict n)) (step≥H (original (suc n)))))
```

被验收一侧是 `ψ (x +ᴸ read0 a)`：它在 `a` 上逐构造子展开 (`YiIrrFoldInst.tail-*`)，零处回到 `ψ x`。
`Lower` 与 `Upper` 各带一个前提 (已有的下界或上界)，结论是加一个 Ω₁ 之后的下界或上界。
上界里加法链的第 n 项不超过参照链的第 2n 项，与 `RR4ChainAdd.c⁺≼c` 同一个办法。

```agda
module Node (x : B.LF) (d : Dom (x +ᴸ tw 2)) where

  node-next : Point one → Point one
  node-next = F.next one tt tt (B.suc x) (λ η e → x +ᴸ read0 η) d

  node-out : Point one → R
  node-out = F.out one tt tt (B.suc x) (λ η e → x +ᴸ read0 η) d

  points : ℕ → Point one
  points = iterate node-next (start one tt tt)

module Lower (X : L.Ordᶜ (L.suc L.zero)) (ex : X L.≅ X)
  (x : B.LF) (dx : Dom x) (low : L.ψ⁰ X ≼ read (ψ x dx))
  (d : Dom (x +ᴸ tw 2)) where

  open Ref X ex
  open Node x d

  tail-lower : ∀ a .(da : Dom (x +ᴸ read0 a)) →
    H (read a) ≼ read (ψ (x +ᴸ read0 a) da)
  tail-lower G.zero da = low
  tail-lower (G.suc a) da =
    raw-suc-lower (ψ (x +ᴸ read0 a) da) (tail-lower a da)
  tail-lower (G.lim f) da = l≼ (λ n → ≼l n
    (tail-lower (f n) (dom-at (λ n → x +ᴸ read0 (f n)) da n)))
  tail-lower (G.lc () c t g) da
  tail-lower (G.em () a) da
  tail-lower G.top da = raw-suc-lower (ψ x dx) low

  out-lower : ∀ (p : Point one) → H (read (coordinate p)) ≼ read (node-out p)
  out-lower (point η e) = tail-lower η
    (dom-branch one tt tt (B.suc x) (λ η e → x +ᴸ read0 η) d η e)

  chain-lower : ∀ n → original n ≼ read (coordinate (points n))
  chain-lower zero = ≼-refl (L.suc L.zero)
  chain-lower (suc n) =
    ≼-trans (step≤H (original n))
    (≼-trans (H-mono (chain-lower n))
    (≼-trans (out-lower (points n))
    (≼-trans (M.≼-+ˡ (read (coordinate (points n)))
        (read (node-out (points n))))
      (proj₂ (read-add-≈ (coordinate (points n)) (node-out (points n)))))))

  append-lower : L.ψ⁰ (X L.+ V.Ω₁) ≼ read (ψ (x +ᴸ tw 2) d)
  append-lower = l≼ (λ n → ≼l n
    (≼-trans (H-mono (chain-lower n)) (out-lower (points n))))

module Upper (X : L.Ordᶜ (L.suc L.zero)) (ex : X L.≅ X)
  (x : B.LF) (dx : Dom x) (high : read (ψ x dx) ≼ L.ψ⁰ X)
  (d : Dom (x +ᴸ tw 2)) where

  open Ref X ex
  open Node x d

  tail-upper : ∀ a .(da : Dom (x +ᴸ read0 a)) →
    read (ψ (x +ᴸ read0 a) da) ≼ H (read a)
  tail-upper G.zero da = high
  tail-upper (G.suc a) da =
    raw-suc-upper (ψ (x +ᴸ read0 a) da) (tail-upper a da)
  tail-upper (G.lim f) da = l≼ (λ n → ≼l n
    (tail-upper (f n) (dom-at (λ n → x +ᴸ read0 (f n)) da n)))
  tail-upper (G.lc () c t g) da
  tail-upper (G.em () a) da
  tail-upper G.top da = raw-suc-upper (ψ x dx) high

  out-upper : ∀ (p : Point one) → read (node-out p) ≼ H (read (coordinate p))
  out-upper (point η e) = tail-upper η
    (dom-branch one tt tt (B.suc x) (λ η e → x +ᴸ read0 η) d η e)

  chain-upper : ∀ n → read (coordinate (points n)) ≼ original (A.dbl n)
  chain-upper zero = ≼-refl (L.suc L.zero)
  chain-upper (suc n) =
    ≼-trans (proj₁ (read-add-≈ (coordinate (points n)) (node-out (points n))))
    (≼-trans (+-mono (chain-upper n)
        (≼-trans (out-upper (points n)) (H-mono (chain-upper n))))
    (≼-trans (dbl-H (original (A.dbl n)))
    (≼-trans (H-mono (o-strict (A.dbl n)))
      (step≥H (original (suc (A.dbl n)))))))

  append-upper : read (ψ (x +ᴸ tw 2) d) ≼ L.ψ⁰ (X L.+ V.Ω₁)
  append-upper = l≼ (λ n → ≼l (A.dbl n)
    (≼-trans (out-upper (points n)) (H-mono (chain-upper n))))
```

## 5 Ω₁·(n+1) 与极限：同值

前提的实例：初项用 §3 的无条件同值，之后每一步用 §4 的两个方向。参照树 `K.reference n` 是 `Level` 里的
Ω₁·(n+1)，`K.omega-reference` 是它们的极限；这两个定义与 "极限严格高于 Ω₁+Ω₁" (`K.not-below-previous`)
都在旧验收文件的参照一侧，这里原样引用。极限处两边都是逐项的 ℕ 极限。

```agda
finite-same : ∀ n → read (ψ (sum n) (sum-dom n)) ≈ᵛ L.ψ⁰ (K.reference n)
finite-same zero = same-on-Ω₁
finite-same (suc n) =
  Upper.append-upper (K.reference n) (K.reference-self n)
    (sum n) (sum-dom n) (proj₁ (finite-same n)) (sum-dom (suc n)) ,
  Lower.append-lower (K.reference n) (K.reference-self n)
    (sum n) (sum-dom n) (proj₂ (finite-same n)) (sum-dom (suc n))

finite-lower : ∀ n → L.ψ⁰ (K.reference n) ≼ read (ψ (sum n) (sum-dom n))
finite-lower n = proj₂ (finite-same n)

nested-same : read (ψ (sum 1) (sum-dom 1)) ≈ᵛ L.ψ⁰ (V.Ω₁ L.+ V.Ω₁)
nested-same = finite-same 1

omega-same : read (ψ limit limit-dom) ≈ᵛ L.ψ⁰ K.omega-reference
omega-same =
  l≼ (λ n → ≼l n (proj₁ (finite-same n))) ,
  l≼ (λ n → ≼l n (proj₂ (finite-same n)))

omega-lower : L.ψ⁰ K.omega-reference ≼ read (ψ limit limit-dom)
omega-lower = proj₂ omega-same
```

`finite-same` 与 `omega-same` 是无条件的闭输出同值 (序数值验收)。输入一侧的对应是按构造平行的
(`sum n` 对 `K.reference n`，`limit` 对 `K.omega-reference`)，本篇没有从层号树到 `Level` 第 1 层的一般解释，
所以结论只对这三族成立，不外推到 `Dom` 里的其它树 (包括 `Ω₁²`)。基本列没有比较：
折叠用加法链，参照用原链，两者的第 n 项不同 (`chain-upper` 用的是参照链的第 2n 项)。
