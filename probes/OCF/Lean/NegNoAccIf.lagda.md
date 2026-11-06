# 去累加, 否定一路 (三): 接口 `NoAccIf` 与 `PtFold` 的盲与边界

> 不含记号. 入口 [NegNoAcc](NegNoAcc.lagda.md). 只读导入构造一路的接口 [NoAccIf](NoAccIf.lagda.md) (定稿 01:40), 不改它. 另导入 [CRwBase](CRwBase.lagda.md), [NegCRwInst](NegCRwInst.lagda.md) 与 [NegNoAccPt](NegNoAccPt.lagda.md) 的小引理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **`I⊞` (实例).** 构造一路说的实例 ($\mathrm{sh}_0\,B\,c=B\boxplus c$, $\mathrm{Adm}_0\,B\,e=B\lhd e$, $\mathrm{nxt}_0=e+1$) 满足 `NoAccIf` 的全部律. 接口的前提可满足.
> 2. **`constShN`, `stayN` (实例, 盲).** 回灌与坐标无关 ($\mathrm{sh}_0\,B\,c=B+1$, `const-sh`) 与进入后世界不动 ($\mathrm{nxt}_0\,B\,e\,a=B$, `stay-nx`) 都满足全部律. 接口不要求回灌依赖坐标, 也不要求世界变大 (同 `NegCRwIf.constShOf`, `stayOf`; `NegCRwInst.stay-no-PH` 说后者落到闭项上地板不带路径).
> 3. **`feed-incomp` (定理, 边界).** 在 `I⊞` 里, 合法的界 $B=1$, 坐标 $c'=\lim(\omega,\omega',\omega',\dots)$ (不合法, 但 `adm-sh` 对一切坐标给出可入). 进入后的世界 $\mathrm{nxt}_0\,B\,(B\boxplus c')=(B\boxplus c')+1$ 有两个第一位置 $B\boxplus\omega$, $B\boxplus\omega'$, 都在 $B$ 之上, **互不为第一位置**. 推论 **`no-cmp`**: 没有不带合法性的比较 ($\neg\forall L\,a\,b.\ a\lhd L\to b\lhd L\to b\lhd a\uplus a\lhd b$). 所以折叠若要在回灌之后的世界里比较两个 "回灌进来的" 层 (例如 CRw 的 `above` 情形: 目标换成回灌进来的层 $i$, 再与别的种类比), 这一次比较需要坐标 $c'$ 合法, 而 $\Omega$-分支是对一切坐标的全函数. 读输入合法因此不只进证书, 也可能进折叠的**定义** (判断; 定理只到 `feed-incomp`).
> 4. **`split⊞`, `cmp-feed` (定理, 正面边界).** 反过来, 回灌进来的层都在旧界之上: $y\lhd B\boxplus c'\Rightarrow y\lhd B\uplus B\lhd y$ (不要合法性, 对一切种类结构). 推论: 目标 $t\lhd B$ 且 $B$ 合法时, 任一 $y\lhd B\boxplus c'$ 都能与 $t$ 比较, 不读 $c'$ 的合法. 所以 `feed-incomp` 只在**两个层都来自回灌**时出现.
> 5. **`pt-blind` (定理, 盲).** `PtFold` 的契约不说强度: 在 $\Omega_1$ 层 (`step S⊥`) 上有一个满足 `PtFold` 全部字段的折叠 `F₀` (相容世界: 界为 $0$), 它把合法的 $\Omega_1$ 结点 $\Omega_1=\sup_c\,c$ 折成 $1$ (`F-Ω₁`, refl). 在合法世界 $(\mathrm{tt},\omega)$ 里 $\omega\lhd\Omega_1$, 但 $F_0\,\omega=\omega\not\lhd 1=F_0\,\Omega_1$. 所以 `F-mono` 只在 `Cw` 里成立是实质的限制, 而 `PtFold` 的四条律 (逐点, 单调, 保合法, 相容世界存在) 分不出这个折叠与构造一路要的折叠. 强度要另用值的定理验收.
>
> **前提实例.** 1, 2: 三个记录都是具体值. 3: $B=1$ 合法 (`tt`), $c'$ 的可入由 `adm-sh` 给出. 4: 任意. 5: 相容世界 $(\mathrm{tt},0)$ (`cw-ex`), $\Omega_1$ 合法 (`Lg-Ω₁`), 世界 $(\mathrm{tt},\omega)$ 合法 (`lg-w₁`).
>
> **只否定什么.** 只否定: (a) 接口的律迫使回灌依赖坐标或世界变大; (b) 回灌之后的世界里, 不读坐标合法也能比较两个回灌进来的层; (c) `PtFold` 的律蕴含任何强度或在一切合法世界里的单调. **不否定**: 构造一路的折叠与闭项 (还没读到); 接口本身 (它的律都可满足); 不比较两个回灌层的折叠设计.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegNoAccIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.NoAccIf
open import OCF.Lean.NegCRwInst using (num; at; lim-not-fin; hs-inj)
open import OCF.Lean.NegNoAccPt using (two)
```

## §1 三个实例

```agda
I⊞ : NoAccIf
I⊞ = record
  { Adm₀ = λ B e → B ⊲ e ; nxt₀ = λ B e a → hs e ; sh₀ = λ B c → B ⊞ c
  ; adm-sh = λ B c → ⊞-fst B c ; lg-sh = λ {B} {c} lB lc → Lg-⊞ B c lB lc ; sh-⊲ = λ B q → ⊞-⊲ B q
  ; nx-up = λ a → hsuc a ; lg-nx = λ a lB le → le ; adm↓ = λ q a′ → ⊲ᴮ-tr q a′ , hself }

constShN : NoAccIf
constShN = record
  { Adm₀ = λ B e → B ⊲ e ; nxt₀ = λ B e a → hs e ; sh₀ = λ B c → hs B
  ; adm-sh = λ B c → hsuc hself ; lg-sh = λ lB lc → lB ; sh-⊲ = λ B q → hself
  ; nx-up = λ a → hsuc a ; lg-nx = λ a lB le → le ; adm↓ = λ q a′ → ⊲ᴮ-tr q a′ , hself }

const-sh : ∀ B c c′ → NoAccIf.sh₀ constShN B c ≡ NoAccIf.sh₀ constShN B c′
const-sh B c c′ = refl

stayN : NoAccIf
stayN = record
  { Adm₀ = λ B e → ⊤ ; nxt₀ = λ B e a → B ; sh₀ = λ B c → B ⊞ c
  ; adm-sh = λ B c → tt ; lg-sh = λ {B} {c} lB lc → Lg-⊞ B c lB lc ; sh-⊲ = λ B q → ⊞-⊲ B q
  ; nx-up = λ a → hself ; lg-nx = λ a lB le → lB ; adm↓ = λ q a′ → tt , q }

stay-nx : ∀ B e a → NoAccIf.nxt₀ stayN B e a ≡ B
stay-nx B e a = refl
```

## §2 回灌之后的世界里, 两个回灌进来的层可以不可比

```agda
ω̂ ω̂′ : Cd
ω̂ = hl num
ω̂′ = hl (λ n → num (suc n))

B₁ : Cd
B₁ = hs hz

c⋆ : Cd
c⋆ = hl (two ω̂ ω̂′)

y₁ y₂ : Cd
y₁ = B₁ ⊞ ω̂
y₂ = B₁ ⊞ ω̂′

Bnum : ∀ k → B₁ ⊞ num k ≡ num (suc k)
Bnum zero = refl
Bnum (suc k) = cong hs (Bnum k)

one≢two : ¬ (num {S⊥} 1 ≡ num 2)
one≢two e = h (hs-inj e)
  where h : ¬ (hz ≡ num {S⊥} 1)
        h ()

¬y₁y₂ : ¬ (y₁ ⊲ y₂)
¬y₁y₂ p = go p refl
  where
  go : ∀ {b} → y₁ ⊲ b → b ≡ y₂ → ⊥
  go hself e = one≢two (cong (λ h → at h 0) e)
  go (hsuc p) ()
  go (hlim n q) refl = lim-not-fin (suc (suc n)) (subst (λ z → y₁ ⊲ z) (Bnum (suc n)) q)

¬y₂y₁ : ¬ (y₂ ⊲ y₁)
¬y₂y₁ p = go p refl
  where
  go : ∀ {b} → y₂ ⊲ b → b ≡ y₁ → ⊥
  go hself e = one≢two (sym (cong (λ h → at h 0) e))
  go (hsuc p) ()
  go (hlim n q) refl = lim-not-fin (suc n) (subst (λ z → y₂ ⊲ z) (Bnum n) q)

module _ where
  open NoAccIf I⊞

  W⋆ : Cd
  W⋆ = nxt₀ B₁ (sh₀ B₁ c⋆) (adm-sh B₁ c⋆)

  feed-incomp : LgB B₁ × (y₁ ⊲ W⋆) × (y₂ ⊲ W⋆) × (B₁ ⊲ y₁) × (B₁ ⊲ y₂) × ¬ (y₁ ⊲ y₂) × ¬ (y₂ ⊲ y₁)
  feed-incomp = tt , hsuc (hlim 0 hself) , hsuc (hlim 1 hself) , ⊞-fst B₁ ω̂ , ⊞-fst B₁ ω̂′ , ¬y₁y₂ , ¬y₂y₁

no-cmp : ¬ (∀ (L a b : Cd) → a ⊲ L → b ⊲ L → (b ⊲ a) ⊎ (a ⊲ b))
no-cmp cmp with cmp W⋆ y₁ y₂ (proj₁ (proj₂ feed-incomp)) (proj₁ (proj₂ (proj₂ feed-incomp)))
... | inj₁ p = ¬y₂y₁ p
... | inj₂ p = ¬y₁y₂ p
```

## §3 回灌进来的层都在旧界之上

```agda
module _ {S : KS} where
  split⊞ : ∀ {w} (B : HB S) c {y} → y ⊲[ w ] B ⊞ c → (y ⊲[ w ] B) ⊎ (B ⊲[ w ] y)
  split⊞ B hz p = inj₁ p
  split⊞ B (hs x) hself = inj₂ (⊞-fst B (hs x))
  split⊞ B (hs x) (hsuc p) = split⊞ B x p
  split⊞ B (hl f) hself = inj₂ (⊞-fst B (hl f))
  split⊞ B (hl f) (hlim n p) = split⊞ B (f n) p
  split⊞ B (hΩ κ g) hself = inj₂ (⊞-fst B (hΩ κ g))
  split⊞ B (hΩ κ g) (hLim e p) = split⊞ B (g _) p

  cmp-feed : ∀ {w} (B : HB S) c {t y} → LgW S w → LgB B → t ⊲[ w ] B → y ⊲[ w ] B ⊞ c →
             (t ⊲[ w ] y) ⊎ (y ⊲[ w ] t)
  cmp-feed B c lw lB pt py with split⊞ B c py
  ... | inj₁ yB = cmpB yB pt lw lB
  ... | inj₂ By = inj₁ (⊲ᴮ-tr pt By)
```

## §4 `PtFold` 不说强度

$\Omega_1$ 层 `step S⊥`. `F₀`: $\Omega_1$ 结点 $\sup g\mapsto F_0(g\,0)+1$, 其余逐构造子. 相容世界: 界为 $0$.

```agda
S₁ : KS
S₁ = step S⊥

F₀ : HB S₁ → Cd
F₀ hz = hz
F₀ (hs x) = hs (F₀ x)
F₀ (hl f) = hl (λ n → F₀ (f n))
F₀ (hΩ (inj₁ ()) g)
F₀ (hΩ (inj₂ _) g) = hs (F₀ (g hz))

Cw₀ : Wd S₁ → Set
Cw₀ w = proj₂ w ≡ hz

⊲hz : ∀ {c : Cd} → c ⊲ hz → c ≡ hz
⊲hz hself = refl

m₀ : ∀ {w a b} → Cw₀ w → a ⊲[ w ] b → F₀ a ⊲ F₀ b
m₀ cw hself = hself
m₀ cw (hsuc p) = hsuc (m₀ cw p)
m₀ cw (hlim n p) = hlim n (m₀ cw p)
m₀ cw (hLim {κ = inj₁ ()} e p)
m₀ {w = u , .hz} {a} refl (hLim {κ = inj₂ _} {g = g} e p) =
  hsuc (subst (λ z → F₀ a ⊲ F₀ (g z)) (⊲hz e) (m₀ refl p))

lg₀ : ∀ h → LgB h → LgB (F₀ h)
lg₀ hz l = tt
lg₀ (hs h) l = lg₀ h l
lg₀ (hl f) (st , l) = (λ n → m₀ {w = tt , hz} refl (st n)) , (λ n → lg₀ (f n) (l n))
lg₀ (hΩ (inj₁ ()) g) l
lg₀ (hΩ (inj₂ _) g) (mo , l) = lg₀ (g hz) (l {w = tt , hz} {c = hz} (tt , tt) hself)

P₀ : PtFold S₁
P₀ = record
  { F = F₀ ; Cw = Cw₀ ; cw-lg = λ { {w = u , .hz} refl → tt , tt } ; cw-ex = (tt , hz) , refl
  ; F-pt = λ f → refl ; F-mono = λ cw lb p → m₀ cw p ; F-lg = lg₀ }
```

$\Omega_1=\sup_c\,\mathrm{up}\,c$ 合法; 折成 $1$; 合法世界 $(\mathrm{tt},\omega)$ 里 $\mathrm{up}\,\omega\lhd\Omega_1$, 像不保持.

```agda
up-⊲ : ∀ {a b : Cd} {β} → a ⊲ b → up a ⊲[ (tt , β) ] up b
up-⊲ hself = hself
up-⊲ (hsuc p) = hsuc (up-⊲ p)
up-⊲ (hlim n p) = hlim n (up-⊲ p)

Lg-up : ∀ (a : Cd) → LgB a → LgB {S₁} (up a)
Lg-up hz l = tt
Lg-up (hs a) l = Lg-up a l
Lg-up (hl f) (st , l) = (λ {w} n → up-⊲ {β = proj₂ w} (st n)) , (λ n → Lg-up (f n) (l n))

Ω₁ : HB S₁
Ω₁ = hΩ (inj₂ tt) up

Lg-Ω₁ : LgB Ω₁
Lg-Ω₁ = (λ { {w = u , β} lw e e′ p → up-⊲ p }) , (λ { {w = u , β} {c} (_ , lβ) e → Lg-up c (lgB⊲ e tt lβ) })

F-Ω₁ : F₀ Ω₁ ≡ hs hz
F-Ω₁ = refl

w₁ : Wd S₁
w₁ = tt , ω̂

lg-w₁ : LgW S₁ w₁
lg-w₁ = tt , ((λ n → hsuc hself) , (λ n → lgn n))
  where lgn : ∀ n → LgB (num {S⊥} n)
        lgn zero = tt
        lgn (suc n) = lgn n

ω⊲Ω₁ : up ω̂ ⊲[ w₁ ] Ω₁
ω⊲Ω₁ = hLim {c = ω̂} hself hself

pt-blind : Σ (PtFold S₁) (λ P → (PtFold.F P Ω₁ ≡ hs hz) × LgB Ω₁ × LgW S₁ w₁ ×
             (up ω̂ ⊲[ w₁ ] Ω₁) × ¬ (PtFold.F P (up ω̂) ⊲ PtFold.F P Ω₁))
pt-blind = P₀ , refl , Lg-Ω₁ , lg-w₁ , ω⊲Ω₁ , (λ { (hsuc ()) })
```

## 结论 (按档)

- **[定理]** 实例 **`I⊞`**, **`constShN`** (`const-sh`), **`stayN`** (`stay-nx`) 满足 `NoAccIf` 全部律; **`feed-incomp`**, **`no-cmp`** (回灌之后两个回灌层可以不可比; 不带合法性的比较不存在); **`split⊞`**, **`cmp-feed`** (回灌层在旧界之上, 与旧界之下的目标可比, 不读坐标合法); **`P₀`** (满足 `PtFold`), `Lg-Ω₁`, `F-Ω₁`, `lg-w₁`, `ω⊲Ω₁`, **`pt-blind`**.
- **[判断]** 读输入合法可能要进折叠的定义 (只在两个回灌层相比时); 是否真的出现, 看构造一路的折叠 (下一篇).
