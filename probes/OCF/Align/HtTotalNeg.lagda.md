# 折叠对一切高度有定义 (一): 两条否定

> 不含记号. 入口 [HtTotal](HtTotal.lagda.md). [HtOutNeg](HtOutNeg.lagda.md) 的 `no-total` 说: 连续且后继处严格变大的 $\Omega$-分支不能在一切坐标上合法, 所以回灌 `Fb` 要 $\Omega$-迭代, 就得在不合法的高度上也有定义. 这里问: **能不能让它在不合法的高度上有定义, 同时在合法的高度上不变?** 折叠用到最高层合法性的地方只有一处: 节点与目标的比较 `rkT` (一次 `cmpH`). 所以有两种做法: 换一个不要合法性的比较 (§3), 或把高度先夹成合法的再折叠 (§2). 两种都在合法的地方不变, 就推出 LPO.
>
> 1. **`no-clamp`**: 若 $\kappa:H\to H$ 总给出合法高度, 且在合法高度上是恒等 ($\mathrm{LgH}\,h\to\kappa\,h\equiv h$), 则 LPO.
> 2. **`no-valid`**: 对任一连续且后继处严格变大的分支 $g$ (正是 `no-total` 的前提), 若一族比较器在一切最高层 $g\,c$ 上全有定义, 并且**在合法坐标 $c$ 上有效** (判上升时确实没有严格的第一位置, 与 [HtCrossRun](HtCrossRun.lagda.md) 的 `Valid` 同义), 则 LPO. 比较器可以看坐标 $c$.
> 3. 推论: `no-valid-top⁺` (最高层取 $1\boxplus g\,c$, 就是回灌用的最高层), `no-valid-all` (比较器对一切最高层有定义, 在合法最高层上有效), **`no-agree`** (比较器在合法坐标上与 `HtFeedFold.rkT` 判得一样, 就有效, 所以推出 LPO).
>
> **前提可满足.** `no-valid` 的分支前提由 `gs` ($g(c)=c$ 的高度, 即 `nb hz (λ _ → hs)`) 满足 (`gs-lim`, `gs-suc`, `Kgs`); 合法高度上的 `rkT` 有效 (`old-valid`). 被否定的只是 "全有定义" 加 "在合法处与原来一致" 这一对.
>
> **范围.** 否定的是比较器层面的一致: 一致要对比较器能收到的一切路径成立. 不否定只在折叠实际发出的那些比较上一致 (判断: 折叠确实会发出证明里那一种比较, 见入口); 不否定输出的值相同而判定不同; 不否定把最高层挪到别处 (不是恒等) 的夹法, [HtTotalClamp](HtTotalClamp.lagda.md) 的 `cl` 就是这样的. 与壁垒: 合法的最高层是被比较的两个位置的字面公共上界, `cmpH` 是有界的比较; 最高层不合法时这个上界不在了, 再要比就是 `noBT`, `no-bra-cmp` 那一族.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTotalNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; ⊲ᴴ-tr; LgH; StH; ss; sl; sL)
open import OCF.Align.HtFeedClosed using (ω⋅)
import OCF.Align.HtFeedFold as Fold
import OCF.Align.HtCrossRun as CR
open import OCF.Align.HtOutRead using (_⊞ᴴ_; ⊞ᴴ-⊲; Cont; c-lim; cont-lg; nb; nb-cont)
open import OCF.Align.HtOutFeed using (top⁺; Lg-top⁺)
open import OCF.Align.HtOutNeg using (no-loop)
```

## §1 LPO 与前缀的 "或"

```agda
LPO : Set
LPO = ∀ (α : ℕ → Bool) → Σ ℕ (λ n → α n ≡ true) ⊎ (∀ n → α n ≡ false)

f≢t : false ≡ true → ⊥
f≢t ()

¬t→f : ∀ b → ¬ (b ≡ true) → b ≡ false
¬t→f true h = ⊥-elim (h refl)
¬t→f false h = refl

∨-r : ∀ b → b ∨ true ≡ true
∨-r true = refl
∨-r false = refl

∨-split : ∀ b b′ → b ∨ b′ ≡ true → (b ≡ true) ⊎ (b′ ≡ true)
∨-split true b′ e = inj₁ refl
∨-split false b′ e = inj₂ e

module Seq (α : ℕ → Bool) where
  any : ℕ → Bool
  any zero = α zero
  any (suc n) = any n ∨ α (suc n)

  any→∃ : ∀ n → any n ≡ true → Σ ℕ (λ k → α k ≡ true)
  any→∃ zero e = zero , e
  any→∃ (suc n) e with ∨-split (any n) (α (suc n)) e
  ... | inj₁ e′ = any→∃ n e′
  ... | inj₂ e′ = suc n , e′

  ∃→any : ∀ n → α n ≡ true → any n ≡ true
  ∃→any zero e = e
  ∃→any (suc n) e = subst (λ b → any n ∨ b ≡ true) (sym e) (∨-r (any n))
```

## §2 夹成合法的高度: 在合法处不能是恒等

高度 $\Lambda_\alpha=\lim(1,\ \lim f_\alpha,\ \lim f_\alpha,\dots)$, $f_\alpha(n)=1$ 若 $\alpha$ 在 $n$ 之前出现过 `true`, 否则 $0$. $\lim f_\alpha$ 总合法 ($f_\alpha$ 单调); $1\lhd\lim f_\alpha$ 当且仅当 $\alpha$ 出现过 `true`. 所以 $\Lambda_\alpha$ 合法当且仅当 $\exists n.\,\alpha(n)$.

读法: 从合法性证明里取第 $0$ 步 $\Lambda(0)\lhd\Lambda(1)$ 的第一个极限下标 (`idx`). 对 $\kappa\,\Lambda_\alpha$ (总合法) 算出 $i$, 再查 $\alpha$ 在 $i$ 之前: 有 `true` 就给出见证; 没有, 则若 $\alpha(n)$ 为真, $\Lambda_\alpha$ 合法, $\kappa\,\Lambda_\alpha\equiv\Lambda_\alpha$, 沿这个等式搬过去的下标指向 $f_\alpha$ 里的 $1$, 也就是 $\alpha$ 在 $i$ 之前出现过 `true`, 矛盾.

```agda
hb₀ : Bool → H
hb₀ true = hs hz
hb₀ false = hz

hb₀-step : ∀ b b′ → hb₀ b ⊲[ azero ] hb₀ (b ∨ b′)
hb₀-step true b′ = hself
hb₀-step false true = hsuc hself
hb₀-step false false = hself

hb₀-lg : ∀ b → LgH (hb₀ b)
hb₀-lg true = tt
hb₀-lg false = tt

hb₀-hit : ∀ {W} b → hs hz ⊲[ W ] hb₀ b → b ≡ true
hb₀-hit true _ = refl
hb₀-hit false ()

tix : ∀ {a b W} → a ⊲[ W ] b → ℕ
tix (hlim n _) = n
tix _ = 0

idx : (x : H) → LgH x → ℕ
idx (hl G) l = tix (proj₁ l 0)
idx _ _ = 0

idx-tr : ∀ {x y} (e : x ≡ y) (l : LgH x) → idx x l ≡ idx y (subst LgH e l)
idx-tr refl l = refl

module Clamp (α : ℕ → Bool) where
  open Seq α

  fα : ℕ → H
  fα n = hb₀ (any n)

  Fα : ℕ → H
  Fα zero = hs hz
  Fα (suc n) = hl fα

  Λα : H
  Λα = hl Fα

  Lg-fα : LgH (hl fα)
  Lg-fα = (λ n → hb₀-step (any n) (α (suc n))) , (λ n → hb₀-lg (any n))

  Lg-Λα : Σ ℕ (λ n → α n ≡ true) → LgH Λα
  Lg-Λα (n , e) = st , lg
    where
    st : ∀ m → Fα m ⊲[ azero ] Fα (suc m)
    st zero = hlim n (subst (λ b → hs hz ⊲[ azero ] hb₀ b) (sym (∃→any n e)) hself)
    st (suc m) = hself
    lg : ∀ m → LgH (Fα m)
    lg zero = tt
    lg (suc m) = Lg-fα

  tix-hit : ∀ {W} (p : hs hz ⊲[ W ] hl fα) → any (tix p) ≡ true
  tix-hit (hlim n P) = hb₀-hit (any n) P

no-clamp : (κ : H → H) → (∀ h → LgH (κ h)) → (∀ h → LgH h → κ h ≡ h) → LPO
no-clamp κ lκ idκ α = go (any i) refl
  where
  open Seq α
  open Clamp α
  i : ℕ
  i = idx (κ Λα) (lκ Λα)
  hit : Σ ℕ (λ n → α n ≡ true) → any i ≡ true
  hit ex = subst (λ j → any j ≡ true) (sym (idx-tr (idκ Λα (Lg-Λα ex)) (lκ Λα)))
                 (tix-hit (proj₁ (subst LgH (idκ Λα (Lg-Λα ex)) (lκ Λα)) 0))
  go : (b : Bool) → any i ≡ b → Σ ℕ (λ n → α n ≡ true) ⊎ (∀ n → α n ≡ false)
  go true e = inj₁ (any→∃ i e)
  go false e = inj₂ (λ n → ¬t→f (α n) (λ en → f≢t (trans (sym e) (hit (n , en)))))
```

## §3 不要合法性的比较: 在合法坐标上不能有效

比较器的判定与 `HtFeedFold` 的同形: 保留 (带严格第一位置的证据) 或上升. `Valid` 同 `HtCrossRun.Val.Valid`.

```agda
data Rk (k t : H) (m : A) : Set where
  keep : StH m k t → Rk k t m
  rise : Rk k t m

Valid : ∀ {k t m} → Rk k t m → Set
Valid (keep _) = ⊤
Valid {k} {t} {m} rise = StH m k t → ⊥

rises : ∀ {k t m} → Rk k t m → Bool
rises (keep _) = false
rises rise = true
```

坐标 $c_\alpha=\lim(2,\ \lim h_\alpha,\ \lim h_\alpha,\dots)$, $h_\alpha(n)=2$ 若 $\alpha$ 在 $n$ 之前出现过 `true`, 否则 $1$. $c_\alpha$ 合法当且仅当 $\exists n.\,\alpha(n)$ (同上). 被比较的是最高层 $g\,c_\alpha\equiv\lim_n g(f_\alpha(n))$ 里第 $0$ 支 $g(2)$ 与第 $1$ 支 $g(\lim h_\alpha)\equiv\lim_n g(h_\alpha(n))$. 后者严格高于前者当且仅当某个 $g(h_\alpha(n))$ 以 $g(2)$ 为第一位置; $h_\alpha(n)=1$ 时不可能, 因为 $g(1)+1\lhd g(2)$, 再有 $g(2)\lhd g(1)$ 就成圈 (`no-loop`). 所以判定 "保留" 给出见证, 判定 "上升" 在 $c_\alpha$ 合法 (即有见证) 时是错的.

```agda
c₁ c₂ : A
c₁ = asuc azero
c₂ = asuc c₁

hb : Bool → A
hb true = c₂
hb false = c₁

hb-step : ∀ b b′ → hb b ⊲ hb (b ∨ b′)
hb-step true b′ = C.self
hb-step false true = C.suc C.self
hb-step false false = C.self

hb-lg : ∀ b → Lg (hb b)
hb-lg true = tt
hb-lg false = tt

module Iter (g : A → H) (cl : ∀ f → g (alim f) ≡ hl (λ n → g (f n))) (cs : ∀ c → hs (g c) ⊲[ azero ] g (asuc c)) (α : ℕ → Bool) where
  open Seq α

  hα : ℕ → A
  hα n = hb (any n)

  fα : ℕ → A
  fα zero = c₂
  fα (suc n) = alim hα

  cα : A
  cα = alim fα

  Lg-cα : Σ ℕ (λ n → α n ≡ true) → Lg cα
  Lg-cα (n , e) = st , lg
    where
    st : ∀ m → fα m ⊲ fα (suc m)
    st zero = C.lim n (subst (λ b → c₂ ⊲ hb b) (sym (∃→any n e)) C.self)
    st (suc m) = C.self
    lg : ∀ m → Lg (fα m)
    lg zero = tt
    lg (suc m) = (λ j → hb-step (any j) (α (suc j))) , (λ j → hb-lg (any j))

  km : g c₂ ⊲[ azero ] g cα
  km = subst (λ X → g c₂ ⊲[ azero ] X) (sym (cl fα)) (hlim 0 hself)

  tm : g (alim hα) ⊲[ azero ] g cα
  tm = subst (λ X → g (alim hα) ⊲[ azero ] X) (sym (cl fα)) (hlim 1 hself)

  hit₁ : ∀ b → g c₂ ⊲[ azero ] g (hb b) → b ≡ true
  hit₁ true _ = refl
  hit₁ false p = ⊥-elim (no-loop (g c₁) (⊲ᴴ-tr (cs c₁) p))

  to′ : StH azero (g c₂) (hl (λ n → g (hα n))) → Σ ℕ (λ k → α k ≡ true)
  to′ (sl n P) = any→∃ n (hit₁ (any n) P)

  to : StH azero (g c₂) (g (alim hα)) → Σ ℕ (λ k → α k ≡ true)
  to R = to′ (subst (StH azero (g c₂)) (cl hα) R)

  of : Σ ℕ (λ k → α k ≡ true) → StH azero (g c₂) (g (alim hα))
  of (n , e) = subst (StH azero (g c₂)) (sym (cl hα)) (sl n (subst (λ b → g c₂ ⊲[ azero ] g (hb b)) (sym (∃→any n e)) hself))

Cmp : (A → H) → Set
Cmp g = ∀ c {k t m} → k ⊲[ m ] g c → t ⊲[ m ] g c → Lg m → Rk k t m

ValidAt : ∀ g → Cmp g → Set
ValidAt g rk = ∀ {c} → Lg c → ∀ {k t m} (p : k ⊲[ m ] g c) (q : t ⊲[ m ] g c) (lm : Lg m) → Valid (rk c p q lm)

no-valid : ∀ (g : A → H) → (∀ f → g (alim f) ≡ hl (λ n → g (f n))) → (∀ c → hs (g c) ⊲[ azero ] g (asuc c)) →
           (rk : Cmp g) → ValidAt g rk → LPO
no-valid g cl cs rk vd α = fin (rk cα km tm tt) (λ ex → vd (Lg-cα ex) km tm tt)
  where
  open Iter g cl cs α
  fin : (x : Rk (g c₂) (g (alim hα)) azero) → (Σ ℕ (λ k → α k ≡ true) → Valid x) → Σ ℕ (λ n → α n ≡ true) ⊎ (∀ n → α n ≡ false)
  fin (keep R) v = inj₁ (to R)
  fin rise v = inj₂ (λ n → ¬t→f (α n) (λ e → v (n , e) (of (n , e))))
```

## §4 推论与前提的实例

**回灌用的最高层.** $1\boxplus g$ 仍连续, 仍严格变大 (`⊞ᴴ` 对 $\lim$ 是逐支的, 对后继保第一位置).

```agda
no-valid-top⁺ : ∀ (g : A → H) → (∀ f → g (alim f) ≡ hl (λ n → g (f n))) → (∀ c → hs (g c) ⊲[ azero ] g (asuc c)) →
                (rk : Cmp (λ c → top⁺ (g c))) → ValidAt (λ c → top⁺ (g c)) rk → LPO
no-valid-top⁺ g cl cs = no-valid (λ c → top⁺ (g c)) (λ f → cong top⁺ (cl f)) (λ c → ⊞ᴴ-⊲ (hs hz) (cs c))
```

**前提的实例.** $g(c)$ 就是坐标 $c$ 本身 (读成高度).

```agda
gs : A → H
gs = nb hz (λ _ h → hs h)

gs-lim : ∀ f → gs (alim f) ≡ hl (λ n → gs (f n))
gs-lim f = refl

gs-suc : ∀ c → hs (gs c) ⊲[ azero ] gs (asuc c)
gs-suc c = hself

Kgs : Cont gs
Kgs = nb-cont tt (λ c h → hsuc hself) (λ c h l → l)
```

**对一切最高层的比较器.** 在合法最高层上有效, 推出 LPO.

```agda
no-valid-all : (rk : ∀ {Λ k t m} → k ⊲[ m ] Λ → t ⊲[ m ] Λ → Lg m → Rk k t m) →
               (∀ {Λ} → LgH Λ → ∀ {k t m} (p : k ⊲[ m ] Λ) (q : t ⊲[ m ] Λ) (lm : Lg m) → Valid (rk p q lm)) → LPO
no-valid-all rk vd = no-valid gs gs-lim gs-suc (λ c → rk) (λ {c} lc → vd (cont-lg Kgs c lc))
```

**与原来的判定一致.** 合法最高层上 `HtFeedFold.rkT` 有效 (`HtCrossRun.Val.rk-valid`), 所以与它判得一样 (都上升或都不上升) 的比较器也有效.

```agda
module Old (Λ : H) (lΛ : LgH Λ) where
  open Fold ω⋅ Λ lΛ using (rkT) renaming (Rk to RkO; keep to keepO; rise to riseO)

  risesO : ∀ {k t m} → RkO k t m → Bool
  risesO (keepO _) = false
  risesO riseO = true

  bitO : ∀ {k t m} → k ⊲[ m ] Λ → t ⊲[ m ] Λ → Lg m → Bool
  bitO p q lm = risesO (rkT p q lm)

  go : ∀ {k t m} (x : RkO k t m) → CR.Val.Valid Λ lΛ x → risesO x ≡ true → StH m k t → ⊥
  go (keepO _) _ ()
  go riseO v _ R = v R

  old-valid : ∀ {k t m} (p : k ⊲[ m ] Λ) (q : t ⊲[ m ] Λ) (lm : Lg m) → bitO p q lm ≡ true → StH m k t → ⊥
  old-valid p q lm = go (rkT p q lm) (CR.Val.rk-valid Λ lΛ p q lm)

valid-of : ∀ {k t m} (x : Rk k t m) (b : Bool) → rises x ≡ b → (b ≡ true → StH m k t → ⊥) → Valid x
valid-of (keep _) b e h = tt
valid-of rise b e h = h (sym e)

no-agree : ∀ (g : A → H) (K : Cont g) → (∀ c → hs (g c) ⊲[ azero ] g (asuc c)) →
           (rk : Cmp (λ c → top⁺ (g c))) →
           (∀ {c} (lc : Lg c) {k t m} (p : k ⊲[ m ] top⁺ (g c)) (q : t ⊲[ m ] top⁺ (g c)) (lm : Lg m) →
              rises (rk c p q lm) ≡ Old.bitO (top⁺ (g c)) (Lg-top⁺ (g c) (cont-lg K c lc)) p q lm) → LPO
no-agree g K cs rk ag =
  no-valid-top⁺ g (c-lim K) cs rk
    (λ {c} lc p q lm → valid-of (rk c p q lm) _ (ag lc p q lm) (Old.old-valid (top⁺ (g c)) (Lg-top⁺ (g c) (cont-lg K c lc)) p q lm))
```
