# φ 的配对否定: k 侧对一切孩子的保留, 实例满足

> 验收文件 (否定). 判决: 反面成立, 编译定理, 无前提. `kstep` 对一切孩子 c 的加强 `KAll` (孩子层 tw n ⊕ ↑c 里槽位在基底 tw n 里的结点, 折到 tw n 时以同一基底槽位保留) 由 `phi` 满足 (`kall-phi`); 所以这一加强连同接口推不出 LPO 或 ⊥.
> "槽位在基底里" 由见证 `InB` 给出: 沿偏移的构造子逐层下行 (孩子任选), 或停在偏移里某个 `Ωₗ` 的下标层侧, 经证据路径推回基底 (`prE`). 规范树 (顶槽位) 只用到后一种; 前一种不在规范域.
> 有限测试 (`refl`): 四个样本保留 (两个核对交出的槽位), 两个槽位层号等于目标层的样本折叠. 不否定什么; 按层号相等判 "能保留" 的加强见 `YiPhiNegKSem` (推出 LPO).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiNegK where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold
open import OCF.Lean.YiPhiIface using (Iface)
open import OCF.Lean.YiPhiCheck using (phi; isΩ; isLim)
```

## 槽位在基底里的见证

`InB a b t`: 层号 a ⊕ b 的槽位 t 其实在基底 a 里. `prE` 给出它在基底里的槽位 (`inj₁` 表示恰是 a 自身, 不严格在里面); 下标层侧经偏移证据 `EvO` 的路径推回. `brE` 是分支换型, 取 `phi` 的保留判定实际用的那一个.

```agda
data InB (a : L) : (b : L) → Pos (a ⊕ b) → Set where
  ib0 : (p : Pos a) → InB a zero p
  ibS : ∀ {b t} → InB a b t → InB a (suc b) (inj₂ t)
  ibL : ∀ {g} (n : ℕ) {t} → InB a (g n) t → InB a (lim g) (n , inj₂ t)
  ibW : ∀ {k h} (c : Tr k) {t} → InB a (h c) t → InB a (Ωₗ k h) (inj₂ (c , inj₂ t))
  ibK : ∀ {k h} (t : Pos⁼ k) → InB a (Ωₗ k h) (inj₁ t)

prE : ∀ {a b t} → InB a b t → EvO a b → Pos⁼ a
prE (ib0 p)   eb           = inj₂ p
prE (ibS i)   eb           = prE i eb
prE (ibL n i) eb           = prE i (eb n)
prE (ibW c i) (v , ek , eb) = prE i (eb c)
prE (ibK t)   (v , ek , eb) = psh v t

liftBr : (a b : L) {K : L} (v : K ≤ a) (t : Pos⁼ K) → Br⁼ a (psh v t) → Br⁼ (a ⊕ b) (psh (v ∙ lift a b) t)
liftBr a zero     v t z = z
liftBr a (suc b)  v t z = liftBr a b v t z
liftBr a (lim g)  v t z = liftBr a (g zero) v t z
liftBr a (Ωₗ k h) v t z = liftBr a (h zero) v t z

brE : ∀ {a b t} (i : InB a b t) (eb : EvO a b) → Br⁼ a (prE i eb) → Br (a ⊕ b) t
brE (ib0 p)   eb           z = z
brE (ibS i)   eb           z = brE i eb z
brE (ibL n i) eb           z = brE i (eb n) z
brE (ibW c i) (v , ek , eb) z = brE i (eb c) z
brE {a} (ibK {h = h} t) (v , ek , eb) z = pshBr (v ∙ lift a (h zero)) t (liftBr a (h zero) v t z)
```

## 保留判定沿 `lift` 下行

偏移的证据取 `Ev⊕` 的形状 (塔的孩子层正是这样). `lemA`: 推到第一个孩子的槽位与 `lift` 路径一起下行; `lemB`: 带见证的槽位一起下行, 到基底时判定只剩 `u`.

```agda
lemA : (a b : L) (ea : Ev a) (eb : EvO a b) {K : L} (v : K ≤ a) (t : Pos⁼ K) {j : L} (u : j ≤ a) {X : Set}
  (Kc : (q : Pos j) → (Br j q → Br⁼ (a ⊕ b) (psh (v ∙ lift a b) t)) → X) (d : X)
  → kp⁼ (a ⊕ b) (Ev⊕ a b ea eb) (psh (v ∙ lift a b) t) (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea (psh v t) u (λ q cv → Kc q (λ z → liftBr a b v t (cv z))) d
lemA a zero     ea eb           v t u Kc d = refl
lemA a (suc b)  ea eb           v t u Kc d = lemA a b ea eb v t u Kc d
lemA a (lim g)  ea eb           v t u Kc d = lemA a (g zero) ea (eb zero) v t u Kc d
lemA a (Ωₗ k h) ea (w , ek , eb) v t u Kc d = lemA a (h zero) ea (eb zero) v t u Kc d

lemB : (a b : L) (ea : Ev a) {t : Pos (a ⊕ b)} (i : InB a b t) (eb : EvO a b) {j : L} (u : j ≤ a) {X : Set}
  (Kc : (q : Pos j) → (Br j q → Br (a ⊕ b) t) → X) (d : X)
  → kp (a ⊕ b) (Ev⊕ a b ea eb) t (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea (prE i eb) u (λ q cv → Kc q (λ z → brE i eb (cv z))) d
lemB a _ ea (ib0 p)   eb           u Kc d = refl
lemB a _ ea (ibS i)   eb           u Kc d = lemB a _ ea i eb u Kc d
lemB a _ ea (ibL n i) eb           u Kc d = lemB a _ ea i (eb n) u Kc d
lemB a _ ea (ibW c i) (w , ek , eb) u Kc d = lemB a _ ea i (eb c) u Kc d
lemB a _ ea (ibK {h = h} t) (w , ek , eb) u Kc d = lemA a (h zero) ea (eb zero) w t u _ d
```

## 加强与实例

`Kept p o`: o 是以 p 为根槽位的结点.

```agda
Kept : ∀ {j} → Pos j → Tr j → Set
Kept {j} p o = Σ (Br j p → Tr j) λ G′ → o ≡ Ω p G′

kept-self : (a : L) (ea : Ev a) (s : Pos⁼ a) (p : Pos a) → s ≡ inj₂ p
  → (F : (q : Pos a) → (Br a q → Br⁼ a s) → Br a q → Tr a) (d : Tr a)
  → Kept p (kp⁼ a ea s self (λ q cv → Ω q (F q cv)) d)
kept-self a ea .(inj₂ p) p refl F d = F p (λ z → z) , refl

child-kept : (a b : L) (ea : Ev a) (eb : EvO a b) (B : Base (a ⊕ b)) (β : Tr a)
  {t : Pos (a ⊕ b)} (G : Br (a ⊕ b) t → Tr (a ⊕ b)) (i : InB a b t) (p : Pos a) → prE i eb ≡ inj₂ p
  → Kept p (ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (Ω t G))
child-kept a b ea eb B β G i p e =
  subst (Kept p)
    (sym (lemB a b ea i eb self (λ q cv → Ω q (λ z → ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (G (cv z)))) _))
    (kept-self a ea (prE i eb) p e (λ q cv z → ψs (a ⊕ b) (Ev⊕ a b ea eb) B a (self ∙ lift a b) β (G (brE i eb (cv z)))) _)
```

`KAll`: 塔第 n+1 项, 目标 tw n, 孩子 c 任意, 结点槽位带见证且严格在基底里. c = 0 时是 `kstep` 的弱形 (只说保留, 不说分支).

```agda
evc : (n : ℕ) (c : Tr (tw n)) → EvO (tw n) (↑ (tw n) c)
evc n c = EvO↑ (tw n) (tw n) (Ev-tw n) self c

KAll : Iface → Set
KAll I = (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (x : Tr (tw (suc n))) (c : Tr (tw n))
  {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
  (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n)) → prE i (evc n c) ≡ inj₂ p
  → Kept p (Iface.ψs I (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β (up x c (Ω t G)))

kall-phi : KAll phi
kall-phi n B β x c G i p e = child-kept (tw n) (↑ (tw n) c) (Ev-tw n) (evc n c) _ _ G i p e

kall-sat : Σ Iface KAll
kall-sat = phi , kall-phi
```

## 有限测试

塔第 2 项折到 tw 1 (n = 1) 与第 3 项折到 tw 2 (n = 2). `top₁` 是 tw 1 的顶槽位 (层号 0).

```agda
top₁ : Pos (tw 1)
top₁ = inj₁ (inj₁ tt)

out : (n : ℕ) (c : Tr (tw n)) (t : Pos (tw n ⊕ ↑ (tw n) c)) → Tr (tw n)
out n c t = ψs (tw (suc n)) (Ev-tw (suc n)) (B₀ _) (tw n) (ink self) (Ωt (tw n)) (up zero c (Ω t (λ _ → zero)))

slot : ∀ {P B C D} → T P B C D → P → P
slot (Ω p _) _ = p
slot _       d = d

-- 孩子 c = Ω top₁ 0 (规范): 孩子层 Ωₗ 0 (λ _ → tw 1), 结点在下标层侧的顶槽位, 交出 tw 1 的顶槽位.
cΩ : Tr (tw 1)
cΩ = Ω top₁ (λ _ → zero)

t-top : isΩ (out 1 cΩ (inj₁ (inj₁ tt)))
t-top = tt
t-top-slot : slot (out 1 cΩ (inj₁ (inj₁ tt))) (inj₂ (zero , inj₁ tt)) ≡ top₁
t-top-slot = refl

-- 同一孩子层, 结点在内层第 1 个孩子 (层号 tw 1) 里的 tw 1 顶槽位 (非规范): 保留.
t-inner : isΩ (out 1 cΩ (inj₂ (suc zero , inj₂ top₁)))
t-inner = tt

-- 孩子 c 是 ℕ 极限 (第 m 项 m 个后继): 结点在第 2 项, 下行两个后继到基底的顶槽位 (非规范): 保留.
sucs : ℕ → Tr (tw 1)
sucs zero    = zero
sucs (suc m) = suc (sucs m)

t-lim : isΩ (out 1 (lim sucs) (suc (suc zero) , inj₂ (inj₂ (inj₂ top₁))))
t-lim = tt

-- 塔第 3 项, 孩子 c 的根槽位在 tw 2 的第 1 个孩子里 (层号 tw 1 + 1); 结点在下标层侧的顶槽位: 保留, 交出 c 的根槽位.
pc : Pos (tw 2)
pc = inj₂ (suc zero , inj₁ tt)

t-deep : isΩ (out 2 (Ω pc (λ _ → zero)) (inj₁ (inj₁ tt)))
t-deep = tt
t-deep-slot : slot (out 2 (Ω pc (λ _ → zero)) (inj₁ (inj₁ tt))) (inj₁ (inj₁ tt)) ≡ pc
t-deep-slot = refl

-- 边界: 结点槽位的层号等于目标层 tw 1 (不严格在基底里), 折叠.
t-eq-suc : isLim (out 1 (suc zero) (inj₁ tt))
t-eq-suc = tt

t-eq-inner : isLim (out 1 cΩ (inj₂ (zero , inj₁ tt)))
t-eq-inner = tt
```

测试样本都在定理 `kall-phi` 的范围里 (见证与基底槽位逐字写出).

```agda
t-top-thm : Kept top₁ (out 1 cΩ (inj₁ (inj₁ tt)))
t-top-thm = kall-phi 1 (B₀ _) (Ωt (tw 1)) zero cΩ (λ _ → zero) (ibK (inj₁ tt)) top₁ refl

t-lim-thm : Kept top₁ (out 1 (lim sucs) (suc (suc zero) , inj₂ (inj₂ (inj₂ top₁))))
t-lim-thm = kall-phi 1 (B₀ _) (Ωt (tw 1)) zero (lim sucs) (λ _ → zero) (ibL 2 (ibS (ibS (ib0 top₁)))) top₁ refl
```
