# 第三站 (一): 实例 3 的三层结构关系与观测

> 不含记号. 入口 [MonoPort5](MonoPort5.lagda.md). 实例 $\Lambda_3=$ `hs (hs (hs hz))`, 世界 $W$ 固定, 目标 $T_0,T_1,T_2$ (都在世界 $W$, 路径字面是 `hsuc` 链).
>
> - **第 $\ge1$ 层的结构关系只写一次** (`RelM ly Low`): 和的构造子 (同 `StrRelDef` 的 $\sqsubseteq_1$, 带自比前提), 加 `nwˡ`, `nwʳ`, `nwᵉ` (只在 `self`; `Run (nw self x) self` 定义性地是 `Run x self`, 三条的语义都是一行), 节点构造子 `ni⊑ r` **对一切节点种类 `r`**, 坐标关系 `Low r` 是参数. 节点构造子的字段形状由树的类型给出: 分支在 `self` 上的值, 坐标按下层关系相关.
> - $\sqsubseteq_1$ = `Rel L1 Low₁` (坐标按 $\sqsubseteq_0$); $\sqsubseteq_2$ = `Rel L2 Low₂`, 两种节点: 第 1 层节点坐标按 $\sqsubseteq_1$ 且两边沿 ⨾ 左脊自比 (`Ok`, 与第 1 层的上下文关系相同: 坐标就是第 1 层的上下文), 第 0 层节点坐标按 $\sqsubseteq_0$.
> - 观测 `O₃`: $T_0$ 上 $\sqsubseteq_0$, $T_1$ 上 $\sqsubseteq_1$, $T_2$ 上 $\sqsubseteq_2$; 满足核 [MonoPort3Gen](MonoPort3Gen.lagda.md) 的全部输出律与 `PreLaw` (`pre₃`). 不要 `LimLaw`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort5Rel {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Data.Unit using (tt)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; D; hz; hs; hself; hsuc; ss; StH; Vs; _⊲[_]_; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.StrRelDef lW using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL)
  renaming (tr to tr₀) public
import OCF.Align.MonoPort3Gen as Gen

Λ₃ L1 L2 : H
Λ₃ = hs (hs (hs hz))
L1 = hs hz
L2 = hs (hs hz)

k0 : hz ⊲[ W ] Λ₃
k0 = hsuc (hsuc (hsuc hself))
k1 : L1 ⊲[ W ] Λ₃
k1 = hsuc (hsuc hself)
k2 : L2 ⊲[ W ] Λ₃
k2 = hsuc hself

module G = Gen Λ₃ tt lW k0
open G using (module P; o₀; OutLaws; PreLaw) public

T₁ : P.Tg W L1 W
T₁ = P.tg C.self k1 lW
T₂ : P.Tg W L2 W
T₂ = P.tg C.self k2 lW

o₁ : P.Df W → D L1 W
o₁ Δ = P.yc Δ T₁
o₂ : P.Df W → D L2 W
o₂ Δ = P.yc Δ T₂
```

## §1 第 $\ge1$ 层的结构关系, 一次写成

```agda
module RelM (ly : H) (Low : ∀ {k} (r : StH W k ly) → Vs ly r W → Vs ly r W → Set) where
  infix 4 _⊑_
  data _⊑_ : D ly W → D ly W → Set where
    n0⊑ : ∀ {x} → n0 ⊑ x
    n1⊑ : n1 ⊑ n1
    ⨾⊑  : ∀ {x y x′ y′} → x ⊑ x → x′ ⊑ x′ → x ⊑ x′ → y ⊑ y′ → (x ⨾ y) ⊑ (x′ ⨾ y′)
    nl⊑ : ∀ {d d′ : ℕ → D ly W} → (∀ n → d n ⊑ d n) → (∀ n → d′ n ⊑ d′ n) → (∀ n → d n ⊑ d′ n) → nl d ⊑ nl d′
    ni⊑ : ∀ {k} (r : StH W k ly) {u u′ : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′} →
          (∀ z z′ → Low r z z′ → u C.self lW z ⊑ u C.self lW z′) →
          (∀ z z′ → Low r z z′ → u′ C.self lW z ⊑ u′ C.self lW z′) →
          (∀ z z′ → Low r z z′ → u C.self lW z ⊑ u′ C.self lW z′) → ni r u ⊑ ni r u′
    nwˡ : ∀ {x x′} → x ⊑ x′ → nw C.self x ⊑ x′
    nwʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ nw C.self x′
    nwᵉ : ∀ {x x′} → nw C.self x ⊑ nw C.self x′ → x ⊑ x′
    tr  : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    u0ˡ : ∀ {x x′} → x ⊑ x′ → (n0 ⨾ x) ⊑ x′
    u0ʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ (n0 ⨾ x′)
    u1ˡ : ∀ {x x′} → x ⊑ x′ → (x ⨾ n0) ⊑ x′
    u1ʳ : ∀ {x x′} → x ⊑ x′ → x ⊑ (x′ ⨾ n0)
    asˡ  : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → (x ⨾ (y ⨾ z)) ⊑ t → ((x ⨾ y) ⨾ z) ⊑ t
    asˡ′ : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → ((x ⨾ y) ⨾ z) ⊑ t → (x ⨾ (y ⨾ z)) ⊑ t
    asʳ  : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → t ⊑ ((x ⨾ y) ⨾ z) → t ⊑ (x ⨾ (y ⨾ z))
    asʳ′ : ∀ {x y z t} → x ⊑ x → y ⊑ y → z ⊑ z → t ⊑ (x ⨾ (y ⨾ z)) → t ⊑ ((x ⨾ y) ⨾ z)
    pre⊑ : ∀ {x x′} {d d′ : ℕ → D ly W} → x ⊑ x → x′ ⊑ x′ → (∀ n → d n ⊑ d n) → (∀ n → d′ n ⊑ d′ n) →
           x ⊑ x′ → (∀ n → d n ⊑ d′ n) → ∀ k → (x ⨾ preL d k) ⊑ (x′ ⨾ nl d′)

  Rf : D ly W → Set
  Rf x = x ⊑ x

  rPre : ∀ {e : ℕ → D ly W} → (∀ n → Rf (e n)) → ∀ k → Rf (preL e k)
  rPre r zero = n0⊑
  rPre r (suc k) = ⨾⊑ (rPre r k) (rPre r k) (rPre r k) (r k)

  rnw : ∀ {x} → Rf x → Rf (nw C.self x)
  rnw r = nwˡ (nwʳ r)

  -- nw 对 ⨾ 的分配 (两个方向), 只在 self
  nwd : ∀ {x y} → Rf x → Rf y → nw C.self (x ⨾ y) ⊑ (nw C.self x ⨾ nw C.self y)
  nwd rx ry = nwˡ (⨾⊑ rx (rnw rx) (nwʳ rx) (nwʳ ry))

  nwd′ : ∀ {x y} → Rf x → Rf y → (nw C.self x ⨾ nw C.self y) ⊑ nw C.self (x ⨾ y)
  nwd′ rx ry = nwʳ (⨾⊑ (rnw rx) rx (nwˡ rx) (nwˡ ry))

  -- 上下文的自比, 沿 ⨾ 的左脊记下每一段 (对树的形状计算, 不对推导反演)
  Ok : D ly W → Set
  Ok (a ⨾ b) = Ok a × Rf b
  Ok x = Rf x

  OkRf : ∀ {x} → Ok x → Rf x
  OkRf {x = n0} o = o
  OkRf {x = n1} o = o
  OkRf {x = a ⨾ b} (oa , rb) = ⨾⊑ (OkRf oa) (OkRf oa) (OkRf oa) rb
  OkRf {x = nl d} o = o
  OkRf {x = ni r u} o = o
  OkRf {x = nκ z v} o = o
  OkRf {x = nw p x} o = o
```

## §2 两层实例

```agda
Low₁ : ∀ {k} (r : StH W k L1) → Vs L1 r W → Vs L1 r W → Set
Low₁ (ss hself) z z′ = z ⊑₀ z′

module R1 = RelM L1 Low₁
open R1 public using () renaming (_⊑_ to _⊑₁_; Rf to Rf₁)

Low₂ : ∀ {k} (r : StH W k L2) → Vs L2 r W → Vs L2 r W → Set
Low₂ (ss hself) z z′ = (z ⊑₁ z′) × (R1.Ok z × R1.Ok z′)
Low₂ (ss (hsuc hself)) z z′ = z ⊑₀ z′

module R2 = RelM L2 Low₂
open R2 public using () renaming (_⊑_ to _⊑₂_; Rf to Rf₂)
```

## §3 观测 $O_3$ 与它的律

```agda
O₃ : OutLaws
O₃ = record
  { _≼_ = λ Δ Δ′ → (o₀ Δ ⊑₀ o₀ Δ′) × ((o₁ Δ ⊑₁ o₁ Δ′) × (o₂ Δ ⊑₂ o₂ Δ′))
  ; L0 = z0 , (R1.n0⊑ , R2.n0⊑)
  ; L⨾ = λ a a′ h k → sq (proj₁ h) (proj₁ k) ,
                       (R1.⨾⊑ (proj₁ (proj₂ a)) (proj₁ (proj₂ a′)) (proj₁ (proj₂ h)) (proj₁ (proj₂ k)) ,
                        R2.⨾⊑ (proj₂ (proj₂ a)) (proj₂ (proj₂ a′)) (proj₂ (proj₂ h)) (proj₂ (proj₂ k)))
  ; Lnl = λ r r′ h → lm (λ n → proj₁ (h n)) ,
                     (R1.nl⊑ (λ n → proj₁ (proj₂ (r n))) (λ n → proj₁ (proj₂ (r′ n))) (λ n → proj₁ (proj₂ (h n))) ,
                      R2.nl⊑ (λ n → proj₂ (proj₂ (r n))) (λ n → proj₂ (proj₂ (r′ n))) (λ n → proj₂ (proj₂ (h n))))
  ; Ltr = λ h k → tr₀ (proj₁ h) (proj₁ k) , (R1.tr (proj₁ (proj₂ h)) (proj₁ (proj₂ k)) , R2.tr (proj₂ (proj₂ h)) (proj₂ (proj₂ k)))
  ; Lu0ˡ = λ h → u0l (proj₁ h) , (R1.u0ˡ (proj₁ (proj₂ h)) , R2.u0ˡ (proj₂ (proj₂ h)))
  ; Lu0ʳ = λ h → u0r (proj₁ h) , (R1.u0ʳ (proj₁ (proj₂ h)) , R2.u0ʳ (proj₂ (proj₂ h)))
  ; Lu1ˡ = λ h → u1l (proj₁ h) , (R1.u1ˡ (proj₁ (proj₂ h)) , R2.u1ˡ (proj₂ (proj₂ h)))
  ; Lu1ʳ = λ h → u1r (proj₁ h) , (R1.u1ʳ (proj₁ (proj₂ h)) , R2.u1ʳ (proj₂ (proj₂ h)))
  ; Lasˡ = λ a b c h → al (proj₁ h) , (R1.asˡ (proj₁ (proj₂ a)) (proj₁ (proj₂ b)) (proj₁ (proj₂ c)) (proj₁ (proj₂ h)) ,
                                       R2.asˡ (proj₂ (proj₂ a)) (proj₂ (proj₂ b)) (proj₂ (proj₂ c)) (proj₂ (proj₂ h)))
  ; Lasˡ′ = λ a b c h → al′ (proj₁ h) , (R1.asˡ′ (proj₁ (proj₂ a)) (proj₁ (proj₂ b)) (proj₁ (proj₂ c)) (proj₁ (proj₂ h)) ,
                                         R2.asˡ′ (proj₂ (proj₂ a)) (proj₂ (proj₂ b)) (proj₂ (proj₂ c)) (proj₂ (proj₂ h)))
  ; Lasʳ = λ a b c h → ar (proj₁ h) , (R1.asʳ (proj₁ (proj₂ a)) (proj₁ (proj₂ b)) (proj₁ (proj₂ c)) (proj₁ (proj₂ h)) ,
                                       R2.asʳ (proj₂ (proj₂ a)) (proj₂ (proj₂ b)) (proj₂ (proj₂ c)) (proj₂ (proj₂ h)))
  ; Lasʳ′ = λ a b c h → ar′ (proj₁ h) , (R1.asʳ′ (proj₁ (proj₂ a)) (proj₁ (proj₂ b)) (proj₁ (proj₂ c)) (proj₁ (proj₂ h)) ,
                                         R2.asʳ′ (proj₂ (proj₂ a)) (proj₂ (proj₂ b)) (proj₂ (proj₂ c)) (proj₂ (proj₂ h)))
  }

open OutLaws O₃ public using (_≼_)

-- 核的部分和在三个目标上的读数, 字面就是部分和
opre : (F : ℕ → P.Df W) {t : H} (Tt : P.Tg W t W) (k : ℕ) →
       P.yc (G.preᴰ F k) Tt ≡ preL (λ n → P.yc (F n) Tt) k
opre F Tt zero = refl
opre F Tt (suc k) = cong (λ s → s ⨾ P.yc (F k) Tt) (opre F Tt k)

pre₃ : PreLaw O₃
pre₃ {a} {a′} {F} {F′} ra ra′ rF rF′ h hF k =
  subst (λ t → (o₀ a ⨾ t) ⊑₀ (o₀ a′ ⨾ nl (λ n → o₀ (F′ n)))) (sym (opre F G.T₀ k)) (pr (proj₁ h) (λ n → proj₁ (hF n)) k) ,
  (subst (λ t → (o₁ a ⨾ t) ⊑₁ (o₁ a′ ⨾ nl (λ n → o₁ (F′ n)))) (sym (opre F T₁ k))
         (R1.pre⊑ (proj₁ (proj₂ ra)) (proj₁ (proj₂ ra′)) (λ n → proj₁ (proj₂ (rF n))) (λ n → proj₁ (proj₂ (rF′ n)))
                  (proj₁ (proj₂ h)) (λ n → proj₁ (proj₂ (hF n))) k) ,
   subst (λ t → (o₂ a ⨾ t) ⊑₂ (o₂ a′ ⨾ nl (λ n → o₂ (F′ n)))) (sym (opre F T₂ k))
         (R2.pre⊑ (proj₂ (proj₂ ra)) (proj₂ (proj₂ ra′)) (λ n → proj₂ (proj₂ (rF n))) (λ n → proj₂ (proj₂ (rF′ n)))
                  (proj₂ (proj₂ h)) (λ n → proj₂ (proj₂ (hF n))) k))
```
