# Ω 形状层号的精确标签 (下标层为第 0 层) 与分支前提取精确读回的关系族

> 验收文件 (读记号)。编译定理, 无前提: 标签 `Lblᵒ` 给 `nd (sΩ zero) h` 加一条 (对带精确读回的孩子一致), `uniqᵒ`、`belowᵒ` (槽位限在读回域 `PosOk` 内)、`topᵉ` 成立; 最小实例的颈结点层号 `YiBVSmall.layer` 有标签 Ω₁ (`lbl-layer`), 它的 Ω 树读作 Ω_{Ω₁} (`top-layer`)。
> 关系族 `Rᵉ`: 与 `YiGLExact.Rˣ` 同形, 第 0 层槽位的分支前提换成精确读回 `Ex⁰` (出路 (a)), 第 0 层的关系仍是 `H.M⁰` (`zero-sameᵉ`), 出口不变。
> 不否定 `Rˣ`; 没有做下标层高于第 0 层的 Ω 形状 (取 `⊥`); 没有给出折叠值的保持。入口: [YiELZero](YiELZero.lagda.md), [YiELLim](YiELLim.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiELOmega where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiKVInst using (Ωω; fsnΩω)
open import OCF.Lean.YiNLRaise using (ΩΩ; fsΩΩ)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; tri; ≤-<)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.EboLeanClosure using (Ctbl-cof)
open import OCF.Align.EBO using () renaming (pred-suc to suc-pred)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiGLFrame using (Lbl; pred<)
open import OCF.Lean.YiELLim using (limAt)
open import OCF.Lean.YiELZero
```

## 标签

后继与 ℕ 极限两条同 `YiGLFrame.Lbl` (极限性质不再作字段)。Ω 形状、下标层为第 0 层: ν 的共尾度是 Ω₁; 每个带精确读回 η 的孩子 d, 层号 `h d` 有标签 μ, 夹在 ν[η] 与 ν 之间。`CofΩ` 是 `LimAt` 在 Ω-共尾一侧的对应物, 只对共尾度同为 Ω₁ 的 u′ 陈述 (唯一性只用到这些)。
孩子的读回用 `YiGLFrame.Lbl`: `↑ zero d` 没有 Ω 形状, 而且在这里引用 `Lblᵒ` 不是结构递归。

```agda
CofΩ : (Tr zero → L) → E.T → Set
CofΩ h ν = ∀ {u′} → NF u′ → E.cof u′ ≡ E.cΩ [] → u′ <ᵀ ν
  → (∀ d η → Ex⁰ η d → E.fsT ν η <ᵀ u′) → ⊥

Lblᵒ : L → E.T → Set
Lblᵒ zero ν = ν ≡ []
Lblᵒ (nd sS h) ν = (E.cof ν ≡ E.c1) × Lblᵒ (h tt) (E.pred ν)
Lblᵒ (nd sL g) ν = (E.cof ν ≡ E.cω) × NF ν
  × (∀ n → Σ E.T λ μ → Lblᵒ (g n) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν))
Lblᵒ (nd (sΩ zero) h) ν = (E.cof ν ≡ E.cΩ []) × NF ν × CofΩ h ν
  × (∀ d η → Ex⁰ η d → Σ E.T λ μ → Lblᵒ (h d) μ × (E.fsT ν η ≤ᵀ μ) × (μ <ᵀ ν))
Lblᵒ (nd (sΩ (nd s k)) h) ν = ⊥

emb : ∀ a {ν} → Lbl a ν → Lblᵒ a ν
emb zero q = q
emb (nd sS h) (e , q) = e , emb (h tt) q
emb (nd sL g) (e , nf , la , k) = e , nf , λ n →
  proj₁ (k n) , emb (g n) (proj₁ (proj₂ (k n))) , proj₂ (proj₂ (k n))
emb (nd (sΩ k) h) ()
```

## 唯一, 槽位严格更低

`PosOk`: 槽位在读回域内, 即沿途每个 Ω 形状的孩子都带精确读回。没有 Ω 形状的层号上它恒成立 (`allok`), 所以 `belowᵒ` 在旧的形状上就是 `YiGLFrame.below`。

```agda
uniqᵒ : ∀ a {ν ν′} → Lblᵒ a ν → Lblᵒ a ν′ → ν ≡ ν′
uniqᵒ zero refl refl = refl
uniqᵒ (nd sS h) {ν} {ν′} (e , q) (e′ , q′) =
  trans (sym (suc-pred ν e)) (trans (cong E.sucT (uniqᵒ (h tt) q q′)) (suc-pred ν′ e′))
uniqᵒ (nd sL g) {ν} {ν′} (e , nf , f) (e′ , nf′ , f′) with tri ν ν′
... | inj₁ lt = ⊥-elim (limAt ν′ e′ nf lt (λ n → ≤-< (proj₁ (proj₂ (proj₂ (f′ n))))
  (subst (_<ᵀ ν) (uniqᵒ (g n) (proj₁ (proj₂ (f n))) (proj₁ (proj₂ (f′ n)))) (proj₂ (proj₂ (proj₂ (f n)))))))
... | inj₂ (inj₁ eq) = eq
... | inj₂ (inj₂ gt) = ⊥-elim (limAt ν e nf′ gt (λ n → ≤-< (proj₁ (proj₂ (proj₂ (f n))))
  (subst (_<ᵀ ν′) (uniqᵒ (g n) (proj₁ (proj₂ (f′ n))) (proj₁ (proj₂ (f n)))) (proj₂ (proj₂ (proj₂ (f′ n)))))))
uniqᵒ (nd (sΩ zero) h) {ν} {ν′} (e , nf , cf , f) (e′ , nf′ , cf′ , f′) with tri ν ν′
... | inj₁ lt = ⊥-elim (cf′ nf e lt (λ d η x → ≤-< (proj₁ (proj₂ (proj₂ (f′ d η x))))
  (subst (_<ᵀ ν) (uniqᵒ (h d) (proj₁ (proj₂ (f d η x))) (proj₁ (proj₂ (f′ d η x)))) (proj₂ (proj₂ (proj₂ (f d η x)))))))
... | inj₂ (inj₁ eq) = eq
... | inj₂ (inj₂ gt) = ⊥-elim (cf nf′ e′ gt (λ d η x → ≤-< (proj₁ (proj₂ (proj₂ (f d η x))))
  (subst (_<ᵀ ν′) (uniqᵒ (h d) (proj₁ (proj₂ (f′ d η x))) (proj₁ (proj₂ (f d η x)))) (proj₂ (proj₂ (proj₂ (f′ d η x)))))))
uniqᵒ (nd (sΩ (nd s k)) h) ()

ChOk : (s : Sh) → Ch s → Set
ChOk sS _ = ⊤
ChOk sL _ = ⊤
ChOk (sΩ zero) d = Σ E.T λ η → Ex⁰ η d
ChOk (sΩ (nd s k)) _ = ⊥

mutual
  PosOk : (a : L) → Pos a → Set
  PosOk (nd s h) (inj₁ _) = ⊤
  PosOk (nd s h) (inj₂ (c , t)) = ChOk s c × PosOk⁼ (h c) t

  PosOk⁼ : (a : L) → Pos⁼ a → Set
  PosOk⁼ a (inj₁ _) = ⊤
  PosOk⁼ a (inj₂ p) = PosOk a p

private
  pos-Ω : ∀ {ν} → E.cof ν ≡ E.cΩ [] → [] <ᵀ ν
  pos-Ω {ν = []} ()
  pos-Ω {ν = x ∷ xs} _ = []<

mutual
  belowᵒ : ∀ a (q : Pos a) → PosOk a q → ∀ {κ ν} → Lblᵒ (at a q) κ → Lblᵒ a ν → κ <ᵀ ν
  belowᵒ (nd sS h) (inj₁ ())
  belowᵒ (nd sS h) (inj₂ (tt , t)) (_ , ok) {ν = ν} lκ (e , q) = ≤-< (below⁼ᵒ (h tt) t ok lκ q) (pred< ν e)
  belowᵒ (nd sL g) (inj₁ ())
  belowᵒ (nd sL g) (inj₂ (n , t)) (_ , ok) lκ (e , _ , f) =
    ≤-< (below⁼ᵒ (g n) t ok lκ (proj₁ (proj₂ (f n)))) (proj₂ (proj₂ (proj₂ (f n))))
  belowᵒ (nd (sΩ zero) h) (inj₁ (inj₁ _)) ok refl (e , _) = pos-Ω e
  belowᵒ (nd (sΩ zero) h) (inj₁ (inj₂ ()))
  belowᵒ (nd (sΩ zero) h) (inj₂ (d , t)) ((η , x) , ok) lκ (e , _ , _ , f) =
    ≤-< (below⁼ᵒ (h d) t ok lκ (proj₁ (proj₂ (f d η x)))) (proj₂ (proj₂ (proj₂ (f d η x))))
  belowᵒ (nd (sΩ (nd s k)) h) q ok lκ ()

  below⁼ᵒ : ∀ a (t : Pos⁼ a) → PosOk⁼ a t → ∀ {κ ν} → Lblᵒ (proj₁ (sl⁼ a t)) κ → Lblᵒ a ν → κ ≤ᵀ ν
  below⁼ᵒ a (inj₁ _) _ lκ lν = inj₂ (uniqᵒ a lκ lν)
  below⁼ᵒ a (inj₂ p) ok lκ lν = inj₁ (belowᵒ a p ok lκ lν)

mutual
  allok : ∀ a {ν} → Lbl a ν → (p : Pos a) → PosOk a p
  allok (nd sS h) (e , q) (inj₁ ())
  allok (nd sS h) (e , q) (inj₂ (tt , t)) = tt , allok⁼ (h tt) q t
  allok (nd sL g) (e , nf , la , k) (inj₁ ())
  allok (nd sL g) (e , nf , la , k) (inj₂ (n , t)) = tt , allok⁼ (g n) (proj₁ (proj₂ (k n))) t
  allok (nd (sΩ k) h) () p

  allok⁼ : ∀ a {ν} → Lbl a ν → (t : Pos⁼ a) → PosOk⁼ a t
  allok⁼ a l (inj₁ _) = tt
  allok⁼ a l (inj₂ p) = allok a l p
```

## 关系族: 第 0 层槽位的分支前提取精确读回

与 `YiGLExact.Rˣ` 的差别只在 `Low⁼ᵉ zero (inj₁ _)` 一行与槽位标签用 `Lblᵒ`。高于第 0 层的槽位的分支前提没有改。

```agda
mutual
  Rᵉ : (ℓ : L) → E.T → Tr ℓ → Set
  Rᵉ zero = H.M⁰
  Rᵉ (nd s h) = H.Mᴴ (Sig (nd s h)) (Lowᵉ (nd s h)) (λ c → Rᵉ (h c)) (λ p → Lblᵒ (at (nd s h) p))

  Lowᵉ : (ℓ : L) (p : Pos ℓ) → E.T → Br ℓ p → Set
  Lowᵉ (nd s h) (inj₂ (c , t)) = Low⁼ᵉ (h c) t
  Lowᵉ (nd (sΩ k) h) (inj₁ t) = Low⁼ᵉ k t

  Low⁼ᵉ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
  Low⁼ᵉ zero (inj₁ _) = Ex⁰
  Low⁼ᵉ (nd s h) (inj₁ _) = Rᵉ (nd s h)
  Low⁼ᵉ zero (inj₂ ())
  Low⁼ᵉ (nd s h) (inj₂ p) = Lowᵉ (nd s h) p

zero-sameᵉ : Rᵉ zero ≡ H.M⁰
zero-sameᵉ = refl

wkᵉ : ∀ ℓ {t x y} → Rᵉ ℓ t x → ℓ ⊢ x ◃ y → Rᵉ ℓ t y
wkᵉ zero = H.mw
wkᵉ (nd s h) = H.mw

low→R : ∀ a {η c} → Low⁼ᵉ a (inj₁ tt) η c → Rᵉ a η c
low→R zero {c = c} x = ex→M⁰ c x
low→R (nd s h) x = x

module Gᵉ (s : Sh) (h : Ch s → L) =
  H.Gen {Sig (nd s h)} {Lowᵉ (nd s h)} {λ c → Rᵉ (h c)} {λ p → Lblᵒ (at (nd s h) p)}
```

## Leaf

前三条同 `YiGLExact.topˣ`。Ω 形状: 结点的余尾下标是第 0 层的标签 0; 带精确读回 η 的孩子 d 上, `h d` 的 Ω 树对着它自己的标签 μ, 再用向下封闭降到 ν[η]。这一条用到分支前提是精确读回: 只有下界证据的 d 上 `h d` 没有标签 (`YiELZero.no-all`)。

```agda
topᵉ : ∀ a {ν} → Lblᵒ a ν → Rᵉ a (E.Ωt ν) (proj₁ (O.Ωt a))
topᵉ zero refl = H.m1 refl H.mz
topᵉ (nd sS h) {ν} (e , q) =
  subst (λ t → Rᵉ (nd sS h) (E.Ωt t) (proj₁ (O.Ωt (nd sS h)))) (suc-pred ν e)
    (H.mΩ (cof-regular (E.pred ν)) q
      (λ η c r → subst (λ t → Rᵉ (nd sS h) t (up zero tt (suc c) (O.z◃ c ◃s)))
        (sym (fs-regular (E.pred ν) η)) (H.mU H.mz (wkᵉ (h tt) (low→R (h tt) r) ◃s))))
topᵉ (nd sL g) {ν} (e , nf , f) = H.mL (Ωω ν e)
  (λ n → subst (λ t → Rᵉ (nd sL g) t (proj₁ (O.Ωt (nd sL g)))) (sym (fsnΩω ν n e))
    (H.mc (Ωt-mono (proj₁ (proj₂ (proj₂ (f n)))))
      (Gᵉ.m-cum sL g (λ m → O.upz {s = sL} {h = g} m (O.Ωt (g m))) n
        (H.mU H.mz (topᵉ (g n) (proj₁ (proj₂ (f n))))))))
topᵉ (nd (sΩ zero) h) {ν} (e , nf , cf , f) = H.mΩ (ΩΩ ν e) refl
  (λ η c x → subst (λ t → Rᵉ (nd (sΩ zero) h) t (proj₁ (O.upz c (O.Ωt (h c)))))
    (sym (fsΩΩ ν η e))
    (H.mc (Ωt-mono (proj₁ (proj₂ (proj₂ (f c η x)))))
      (H.mU H.mz (topᵉ (h c) (proj₁ (proj₂ (f c η x)))))))
topᵉ (nd (sΩ (nd s k)) h) ()
```

## 最小实例的颈结点层号

`YiBVSmall.layer = nd (sΩ zero) child` 的标签是 Ω₁: 孩子的标签由 `child-lbl` 给出; `CofΩ` 在 Ω₁ 上空成立 (低于 Ω₁ 的标准形可数, 共尾度不是 Ω₁)。

```agda
lbl-layer : Lblᵒ S.layer Ω₁
lbl-layer = refl , nf-Ω₁ , (λ nf′ e′ lt _ → Ctbl-cof (ctbl< nf′ lt) e′) , λ d η x →
  let r = child-lbl d x in
  proj₁ r , emb (S.child d) (proj₁ (proj₂ r)) , proj₁ (proj₂ (proj₂ r)) , proj₂ (proj₂ (proj₂ r))

top-layer : Rᵉ S.layer (E.Ωt Ω₁) (proj₁ (O.Ωt S.layer))
top-layer = topᵉ S.layer lbl-layer

below-layer : ∀ d {η} → Ex⁰ η d → (t : Pos⁼ (S.child d)) → PosOk⁼ (S.child d) t
  → ∀ {κ} → Lblᵒ (proj₁ (sl⁼ (S.child d) t)) κ → κ <ᵀ Ω₁
below-layer d {η} x t ok lκ = belowᵒ S.layer (inj₂ (d , t)) ((η , x) , ok) lκ lbl-layer
```
