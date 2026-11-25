# 比较表的对角条目: 在一个 ℕ 极限孩子上就弱判等

> 判决: 编译定理, 不读记号, 不改树、折叠、合法性. 现行行比较两个孩子只经 `proj₁ r c c′` (`row-diag`: 同一个变量 c 给两边时卡在 `proj₁ r c c`), 保留判定 `kpʳ` 在槽位孩子与路径孩子的对角上恒为空 (`kp-diag`); 所以 "同一孩子的见证" 只能是下标的函数. 塔第 1 项上, 任何一列 (孩子 c ↦ 第 c 层与第 c⋆ 层之间可缺的字面路径) 只要在 c⋆ = sᵐ ωᵉ 处有条目, 就对康托族弱判等 (`ColW.wdecα`, 无前提); 加 ℕ → Bool 的函数外延得 WLPO (`col→wlpo`, 条件). 表的对角 (`Diag`, `all→wlpo`) 与沿目标逐孩子给的可缺路径 (`pth→wlpo`) 都是列.
> 前提: 数字孩子上对角可满足 (`diag-nat`); 有字面相等的判定就有处处对角的表 (`dec→tab`), 所以前提不自相矛盾. 康托族是合法的树, 在 α₀ 处字面是 ωᵉ (`cα-α₀`).
> 不否定什么: 数字列的整列填表 (`AuditDFin.colFin` 一类), 对角之外按字面路径给的条目, 不经表与路径的写法 (换基, 一致目标), 保留判定 K 的变体 (保留不要求字面路径, 类型逼不出 "别处为空"). 与 `YiTBObs.exact→wdec` 的差别: 那里 "别处为空" 是前提, 这里由 "没有字面路径" 逼出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDGDiag where
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; RbS; dW; nat; h₁; tb; tb-nat)
open import OCF.Lean.YiTBTab using (ωᵉ; dbl)
open import OCF.Lean.YiTBObs using (d; NoLim; nlD)
open import OCF.Lean.YiAbsObs using (Dec′; IsJust; AllF; WLPO)
open import OCF.Lean.YiKFKeep using (Pv; kpʳ)
open import OCF.Lean.YiKFFold using (module FC)
```

## 行只在表上派发

嵌入在孩子 c (树给), 目标经孩子 c′ (路径给), 两份数据分开进来; 比较只在 `proj₁ r c c′`. `kpʳ` 那一行在对角上也为空 (`kpᶜ` 另有来源表与地板两条退路).

```agda
row-diag : ∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c (v : j ≤ h c) ot β x y e
  → Σ _ λ F → Σ _ λ G → Σ _ λ H → FC.ψ (nd (sΩ k) h) o r pv B j (inc c v) ot β (up x c y e) ≡ dW (proj₁ r c c) F G H
row-diag k h o r pv B j c v ot β x y e = _ , _ , _ , refl

kp-diag : ∀ k h (o : Ok (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) c t {j} (v : j ≤ h c)
  → kpʳ (nd (sΩ k) h) o pv (inj₂ (c , t)) (inc c v) ≡ nothing
kp-diag k h o pv c t v = refl

Tab : Set
Tab = RbS (sΩ zero) h₁

tab-tw1 : Rb (tw 1) ≡ (Tab × ((c : Tr zero) → Rb (h₁ c)))
tab-tw1 = refl
```

## 康托族

`fα α n` 是第 n 个偶数, α n 为真时多一个后继; 相邻项总是严格上升, 所以族里每一项都是合法的 ℕ 极限.

```agda
sh : Bool → Tr zero → Tr zero
sh false x = x
sh true  x = suc x

stp : (b b′ : Bool) (x : Tr zero) → zero ⊢ sh b x ◃ sh b′ (suc (suc x))
stp false false x = ◃t ◃s ◃s
stp false true  x = ◃t ◃s (◃t ◃s ◃s)
stp true  false x = ◃s
stp true  true  x = ◃t ◃s ◃s

fα : (ℕ → Bool) → ℕ → Tr zero
fα α n = sh (α n) (dbl n)

cα : (ℕ → Bool) → Tr zero
cα α = lim (fα α) (λ n → stp (α n) (α (suc n)) (dbl n))

cα-α₀ : cα (λ _ → false) ≡ ωᵉ
cα-α₀ = refl

sᵐ : ℕ → Tr zero → Tr zero
sᵐ zero    x = x
sᵐ (suc m) x = suc (sᵐ m x)
```

## 字面路径只在 α 处处为假时有

`HasL`: 沿后继形状的孩子走到 ℕ 极限或 Ω 形状. `noHL` 推广 `YiTBObs.noL`: 这样的层号没有通到有限后继链层号的路径. `peel` 剥掉两边同一层后继形状.

```agda
HasL : L → Set
HasL zero          = ⊥
HasL (nd sS g)     = HasL (g tt)
HasL (nd sL g)     = ⊤
HasL (nd (sΩ _) _) = ⊤

noHL : ∀ {b j} → HasL j → (x : Tr zero) → NoLim x → Pth b j (h₁ x) → ⊥
noHL hj zero      nl self      = hj
noHL {b} hj (suc x) nl self    = noHL {b} hj x nl self
noHL hj (suc x)   nl (inc c v) = noHL hj x nl v
noHL hj (suc x)   nl (inu vs)  = noHL hj x nl (vs tt)
noHL hj (lim f a) ()

nlSh : (b : Bool) (x : Tr zero) → NoLim x → NoLim (sh b x)
nlSh false x nl = nl
nlSh true  x nl = nl

dAt : ℕ → L → ℕ
dAt n (nd sL g) = d (g n)
dAt n _         = 0

nsuc : (x : ℕ) → x ≡ suc x → ⊥
nsuc zero    ()
nsuc (suc x) e = nsuc x (cong pred e)

ex : (b : Bool) (x : Tr zero) → d (h₁ x) ≡ d (h₁ (sh b x)) → b ≡ false
ex false x e = refl
ex true  x e = ⊥-elim (nsuc (d (h₁ x)) e)

eqAll : ∀ α → h₁ ωᵉ ≡ h₁ (cα α) → AllF α
eqAll α e n = ex (α n) (dbl n) (cong (dAt n) e)

module _ (α : ℕ → Bool) where
  nlF : ∀ n → NoLim (fα α n)
  nlF n = nlSh (α n) (dbl n) (nlD n)

  pathA : ∀ {b j ℓ} → Pth b j ℓ → j ≡ h₁ ωᵉ → ℓ ≡ h₁ (cα α) → AllF α
  pathA self      e₁   e₂   = eqAll α (trans (sym e₁) e₂)
  pathA (inc c v) refl refl = ⊥-elim (noHL tt (fα α c) (nlF c) v)
  pathA (inu vs)  refl refl = ⊥-elim (noHL tt (fα α 0) (nlF 0) (vs 0))
  pathA (ink v)   e₁   ()

  pathB : ∀ {b j ℓ} → Pth b j ℓ → j ≡ h₁ (cα α) → ℓ ≡ h₁ ωᵉ → AllF α
  pathB self      e₁   e₂   = eqAll α (trans (sym e₂) e₁)
  pathB (inc c v) refl refl = ⊥-elim (noHL tt (dbl c) (nlD c) v)
  pathB (inu vs)  refl refl = ⊥-elim (noHL tt (dbl 0) (nlD 0) (vs 0))
  pathB (ink v)   e₁   ()

chS : L → L
chS (nd sS g) = g tt
chS _         = zero

peel : ∀ {b} (x x′ : Tr zero) {j ℓ} → Pth b j ℓ → j ≡ h₁ (suc x′) → ℓ ≡ h₁ (suc x) → Pth b (h₁ x′) (h₁ x)
peel {b} x x′ self e₁ e₂ = subst (Pth b (h₁ x′)) (cong chS (trans (sym e₁) e₂)) self
peel x x′ (inc c v) refl refl = inc tt self ∙ v
peel x x′ (inu vs)  refl refl = inc tt self ∙ vs tt
peel x x′ (ink v)   e₁   ()

peelᵐ : ∀ {b} (m : ℕ) (x x′ : Tr zero) → Pth b (h₁ (sᵐ m x′)) (h₁ (sᵐ m x)) → Pth b (h₁ x′) (h₁ x)
peelᵐ zero    x x′ p = p
peelᵐ (suc m) x x′ p = peelᵐ m x x′ (peel (sᵐ m x) (sᵐ m x′) p refl refl)
```

## 一列在 c⋆ 处有条目就弱判等

c⋆ = sᵐ m ωᵉ; m = 2 是 `YiCTCall` 那一格 (路径经孩子 d 的二次后继) 在 d = ωᵉ 时的形状 (见 [YiDGCell](YiDGCell.lagda.md)). 列在 sᵐ m (cα α) 处有条目就有字面路径, 剥掉后继后由 `pathA`, `pathB` 得 α 处处为假; 没有条目就与 c⋆ 处的条目矛盾.

```agda
Col : ℕ → Set
Col m = (c : Tr zero) → Maybe ((h₁ (sᵐ m ωᵉ) ≤ h₁ c) ⊎ (h₁ c ≤ h₁ (sᵐ m ωᵉ)))

module ColW (m : ℕ) (col : Col m) where
  c⋆ : Tr zero
  c⋆ = sᵐ m ωᵉ

  wdecα : IsJust (col c⋆) → ∀ α → AllF α ⊎ (c⋆ ≡ sᵐ m (cα α) → ⊥)
  wdecα j α = go (col (sᵐ m (cα α))) refl
    where
    go : (u : Maybe ((h₁ c⋆ ≤ h₁ (sᵐ m (cα α))) ⊎ (h₁ (sᵐ m (cα α)) ≤ h₁ c⋆)))
       → col (sᵐ m (cα α)) ≡ u → AllF α ⊎ (c⋆ ≡ sᵐ m (cα α) → ⊥)
    go (just (inj₁ p)) q = inj₁ (pathA α (peelᵐ m (cα α) ωᵉ p) refl refl)
    go (just (inj₂ p)) q = inj₁ (pathB α (peelᵐ m ωᵉ (cα α) p) refl refl)
    go nothing         q = inj₂ (λ e → subst IsJust q (subst (λ c → IsJust (col c)) e j))

FunextB : Set
FunextB = {α β : ℕ → Bool} → (∀ n → α n ≡ β n) → α ≡ β

back : FunextB → ∀ m α → AllF α → sᵐ m ωᵉ ≡ sᵐ m (cα α)
back fe m α af = cong (λ β → sᵐ m (cα β)) (fe {α = λ _ → false} {β = α} (λ n → sym (af n)))

col→wlpo : FunextB → (m : ℕ) (col : Col m) → IsJust (col (sᵐ m ωᵉ)) → WLPO
col→wlpo fe m col j α with ColW.wdecα m col j α
... | inj₁ af = inj₁ af
... | inj₂ ne = inj₂ (λ af → ne (back fe m α af))
```

表的对角: 取表在 c⋆ 那一列. 沿目标逐孩子给的可缺路径 (一致目标 `inu` 的可缺版本): 只有一个方向的列.

```agda
module Diag (t : Tab) (m : ℕ) = ColW m (λ c → t c (sᵐ m ωᵉ))

wlpo : FunextB → (t : Tab) (m : ℕ) → IsJust (t (sᵐ m ωᵉ) (sᵐ m ωᵉ)) → WLPO
wlpo fe t m = col→wlpo fe m (λ c → t c (sᵐ m ωᵉ))

all→wdecα : (t : Tab) → (∀ c → IsJust (t c c)) → ∀ α → AllF α ⊎ (ωᵉ ≡ cα α → ⊥)
all→wdecα t all = Diag.wdecα t 0 (all ωᵉ)

all→wlpo : FunextB → (t : Tab) → (∀ c → IsJust (t c c)) → WLPO
all→wlpo fe t all = wlpo fe t 0 (all ωᵉ)

Pth⋆ : ℕ → Set
Pth⋆ m = (c : Tr zero) → Maybe (h₁ (sᵐ m ωᵉ) ≤ h₁ c)

up₁ : ∀ {A B : Set} → Maybe A → Maybe (A ⊎ B)
up₁ (just a) = just (inj₁ a)
up₁ nothing  = nothing

isj₁ : ∀ {A B : Set} (u : Maybe A) → IsJust u → IsJust (up₁ {B = B} u)
isj₁ (just a) _ = tt

pth→wlpo : FunextB → (m : ℕ) (o : Pth⋆ m) → IsJust (o (sᵐ m ωᵉ)) → WLPO
pth→wlpo fe m o j = col→wlpo fe m (λ c → up₁ (o c)) (isj₁ (o (sᵐ m ωᵉ)) j)
```

## 前提可满足

数字孩子的对角由 `YiTBRow.tb` 给出; 有字面相等的判定, 就有处处对角的表.

```agda
diag-nat : ∀ n → IsJust (tb (nat n) (nat n))
diag-nat n = subst IsJust (sym (tb-nat n n)) tt

module _ (D : (c c′ : Tr zero) → Dec′ (c ≡ c′)) where
  mk : ∀ {c c′} → Dec′ (c ≡ c′) → Maybe ((h₁ c′ ≤ h₁ c) ⊎ (h₁ c ≤ h₁ c′))
  mk {c} (inj₁ e) = just (inj₁ (subst (λ z → h₁ z ≤ h₁ c) e self))
  mk     (inj₂ _) = nothing

  tabD : Tab
  tabD c c′ = mk (D c c′)

  isj : ∀ {c} (u : Dec′ (c ≡ c)) → IsJust (mk u)
  isj (inj₁ e)  = tt
  isj (inj₂ ne) = ⊥-elim (ne refl)

  dec→tab : ∀ c → IsJust (tabD c c)
  dec→tab c = isj (D c c)
```
