# ValC (二): 折叠的值的底层引理 (累加, 链, 地板, 决定)

> 不含记号. 入口 [ValC](ValC.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 只导入 stdlib, `OCF.Lean.CRw*` 与 [ValCRel](ValCRel.lagda.md).
>
> 这一篇: 部分积、部分和、回灌链在值关系下的单调 (对子列, 对界), 地板值合法 (`Mo-top`), 折叠的输出不低于 $1$ (`one≤`), 以及 "留下的结点" 的两条比较 (`keepR`, `keepKK`, `keepMo`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.ValCBase (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤′_; ≤′-refl; ≤′-step; _<′_)
open import Data.Nat.Properties using (<⇒<′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
```

## §1 累加与链

```agda
module Ac0 (t : Cd) where
  open L t

  mul-mono : ∀ {a a′} → a ≤ a′ → ∀ n → mul a n ≤ mul a′ n
  mul-mono p zero = p
  mul-mono p (suc n) = ⊞-mono (mul-mono p n) p

  Mo-mul : ∀ a → Mo a → ∀ n → Mo (mul a n)
  Mo-mul a m zero = m
  Mo-mul a m (suc n) = Mo-⊞ (mul a n) a (Mo-mul a m n) m

  ≤mul : ∀ a n → a ≤ mul a n
  ≤mul a zero = ≤-refl a
  ≤mul a (suc n) = ≤-trans (≤mul a n) (≤⊞ (mul a n) a)

  Mo-Σ : ∀ F → (∀ n → Mo (F n)) → ∀ n → Mo (Σ⁺ F n)
  Mo-Σ F m zero = m 0
  Mo-Σ F m (suc n) = Mo-⊞ _ _ (Mo-Σ F m n) (m (suc n))

  Σ-ge : ∀ F n → F n ≤ Σ⁺ F n
  Σ-ge F zero = ≤-refl _
  Σ-ge F (suc n) = ≤⊞ˡ (Σ⁺ F n) (F (suc n))

  Σ-idx : ∀ F {i j} → i ≤′ j → Σ⁺ F i ≤ Σ⁺ F j
  Σ-idx F ≤′-refl = ≤-refl _
  Σ-idx F (≤′-step p) = ≤-trans (Σ-idx F p) (≤⊞ _ _)

  lw : ∀ {i j} → suc i ≤′ j → i ≤′ j
  lw ≤′-refl = ≤′-step ≤′-refl
  lw (≤′-step p) = ≤′-step (lw p)

  skip : ∀ F {i j} → suc i ≤′ j → Σ⁺ F i ⊞ F j ≤ Σ⁺ F j
  skip F ≤′-refl = ≤-refl _
  skip F (≤′-step p) = ⊞-monoˡ _ (Σ-idx F (lw p))

  -- 对子列: F n ≤ G (σ n), σ 严格增 ⟹ 部分和 Σ F n ≤ Σ G (σ n)
  Σ-sub : ∀ F G σ → Inc σ → (∀ n → F n ≤ G (σ n)) → ∀ n → Σ⁺ F n ≤ Σ⁺ G (σ n)
  Σ-sub F G σ i h zero = ≤-trans (h 0) (Σ-ge G (σ 0))
  Σ-sub F G σ i h (suc n) = ≤-trans (⊞-mono (Σ-sub F G σ i h n) (h (suc n))) (skip G (<⇒<′ (i n)))

  Σ-pt : ∀ F G → (∀ n → F n ≤ G n) → ∀ n → Σ⁺ F n ≤ Σ⁺ G n
  Σ-pt F G h zero = h 0
  Σ-pt F G h (suc n) = ⊞-mono (Σ-pt F G h n) (h (suc n))

  -- n+1 份 F 不超过前 n+1 个部分积的折叠之和
  mulΣ : ∀ (u : H t) (F : ℕ → H t) → (∀ n → u ≤ F n) → ∀ n → mul u n ≤ Σ⁺ F n
  mulΣ u F h zero = h 0
  mulΣ u F h (suc n) = ⊞-mono (mulΣ u F h n) (h (suc n))
```

**回灌链** (同 Fab5 的 `ch`): 两条链的第 $k$ 点互相 `≤`, 若 "界 $b_1\le b_2$ 时 $k_L\,b_1\le k_R\,b_2$" (界都在地板之上, 值合法).

```agda
  Bnd : H t → H t → Set
  Bnd b b′ = Mo b × Mo b′ × (top b⊥ t ≤ b) × (b ≤ b′)

  bnd-refl : ∀ {b} → Mo b → top b⊥ t ≤ b → Bnd b b
  bnd-refl {b} m p = m , m , p , ≤-refl b

  KP : (H t → H t) → Set
  KP k = ∀ b → Mo b → top b⊥ t ≤ b → Mo (k b)

  chM : ∀ b k → Mo b → top b⊥ t ≤ b → KP k → ∀ n → Mo (chain b k n)
  chM b k mb tb mk zero = mk b mb tb
  chM b k mb tb mk (suc n) = Mo-⊞ _ _ (chM b k mb tb mk n)
    (mk _ (Mo-⊞ b _ mb (chM b k mb tb mk n)) (≤-trans tb (≤⊞ b _)))

  chLe : ∀ {b b′} kL kR → Bnd b b′ → KP kL → KP kR →
         (∀ {b₁ b₂} → Bnd b₁ b₂ → kL b₁ ≤ kR b₂) → ∀ n → chain b kL n ≤ chain b′ kR n
  chLe kL kR B mL mR h zero = h B
  chLe {b} {b′} kL kR B@(mb , mb′ , tb , bb) mL mR h (suc n) =
    ⊞-mono (chLe kL kR B mL mR h n)
      (h (Mo-⊞ b _ mb (chM b kL mb tb mL n) , Mo-⊞ b′ _ mb′ (chM b′ kR mb′ (≤-trans tb bb) mR n) ,
          ≤-trans tb (≤⊞ b _) , ⊞-mono bb (chLe kL kR B mL mR h n)))

  chLe-hl : ∀ {b b′} kL kR → Bnd b b′ → KP kL → KP kR →
            (∀ {b₁ b₂} → Bnd b₁ b₂ → kL b₁ ≤ kR b₂) → hl (chain b kL) ≤ hl (chain b′ kR)
  chLe-hl kL kR B mL mR h = l≤l (λ n → n) idInc (chLe kL kR B mL mR h)
```

## §2 嵌入与地板

```agda
up-mono : ∀ {x a b} → LeAt x a b → LeAt (hs x) (up a) (up b)
up-mono Rel.z≤ = Rel.z≤
up-mono (Rel.s≤s p) = Rel.s≤s (up-mono p)
up-mono (Rel.≤s p) = Rel.≤s (up-mono p)
up-mono (Rel.l≤l σ i h) = Rel.l≤l σ i (λ n → up-mono (h n))
up-mono (Rel.≤l n p) = Rel.≤l n (up-mono p)
up-mono (Rel.≤Ω c e m p) = Rel.≤Ω c e m (up-mono p)
up-mono (Rel.Ω≤Ω e h) = Rel.Ω≤Ω e (λ c mc → up-mono (h c mc))

Mo-up : ∀ {x} a → MoAt x a → MoAt (hs x) (up a)
Mo-up hz m = tt
Mo-up (hs a) m = Mo-up a m
Mo-up (hl f) m = λ n → Mo-up (f n) (m n)
Mo-up (hΩ κ g) (mo , mh) = (λ c c′ mc mc′ p → up-mono (mo c c′ mc mc′ p)) , (λ c mc → Mo-up (g _) (mh c mc))

ι-mono : ∀ {f : ℕ → Cd} n {a b} → LeAt (f n) a b → LeAt (hl f) (ι n a) (ι n b)
ι-mono n Rel.z≤ = Rel.z≤
ι-mono n (Rel.s≤s p) = Rel.s≤s (ι-mono n p)
ι-mono n (Rel.≤s p) = Rel.≤s (ι-mono n p)
ι-mono n (Rel.l≤l σ i h) = Rel.l≤l σ i (λ k → ι-mono n (h k))
ι-mono n (Rel.≤l k p) = Rel.≤l k (ι-mono n p)
ι-mono n (Rel.≤Ω c e m p) = Rel.≤Ω c e m (ι-mono n p)
ι-mono n (Rel.Ω≤Ω e h) = Rel.Ω≤Ω e (λ c mc → ι-mono n (h c mc))

Mo-ι : ∀ {f : ℕ → Cd} n a → MoAt (f n) a → MoAt (hl f) (ι n a)
Mo-ι n hz m = tt
Mo-ι n (hs a) m = Mo-ι n a m
Mo-ι n (hl g) m = λ k → Mo-ι n (g k) (m k)
Mo-ι n (hΩ κ g) (mo , mh) = (λ c c′ mc mc′ p → ι-mono n (mo c c′ mc mc′ p)) , (λ c mc → Mo-ι n (g _) (mh c mc))

Mo-top : ∀ t → MoAt t (top b⊥ t)
Mo-ΣT : ∀ (f : ℕ → Cd) n → MoAt (hl f) (ΣT S⊥ hz f n)
Mo-top hz = tt
Mo-top (hs x) = (λ c c′ mc mc′ p → up-mono p) , (λ c mc → Mo-up c mc)
Mo-top (hl f) = Mo-ΣT f
Mo-top (hΩ () _)
Mo-ΣT f zero = Mo-ι 0 _ (Mo-top (f 0))
Mo-ΣT f (suc n) = L.Mo-⊞ (hl f) _ _ (Mo-ΣT f n) (Mo-ι (suc n) _ (Mo-top (f (suc n))))
```

## §3 留下的结点

折叠留下的结点的种类 $\kappa_1$ 在第 $t$ 层, 层是 $k$ (`e₁`), 坐标经 `fr` 回到第 $k$ 层, `fr ∘ toK` 是搬运 (`ft`). 三条: 在一个坐标处取一支 (`keepR`); 两个留下的结点逐支比较 (`keepKK`); 值合法 (`keepMo`).

```agda
module _ (t : Cd) where
  open L t

  keepR : ∀ {k} (κ₁ : K (T t)) (e₁ : lvK t κ₁ ≡ k) (fr : E (T t) κ₁ → H k) →
          (∀ c → fr (toK t κ₁ c) ≡ subst H e₁ c) →
          ∀ (u : H k → H t) {z} c → LeAt k c (top b⊥ k) → MoAt k c → z ≤ u c → z ≤ hΩ κ₁ (λ c′ → u (fr c′))
  keepR κ₁ refl fr ft u c bd mc p =
    ≤Ω c (→lle t κ₁ c _ bd) (→lmo t κ₁ c mc) (subst (λ w → _ ≤ u w) (sym (ft c)) p)

  keepKK : ∀ {k} (κ₁ κ₂ : K (T t)) (e₁ : lvK t κ₁ ≡ k) (e₂ : lvK t κ₂ ≡ k)
           (fr₁ : E (T t) κ₁ → H k) (fr₂ : E (T t) κ₂ → H k) →
           (∀ c → fr₁ (toK t κ₁ c) ≡ subst H e₁ c) → (∀ c → fr₂ (toK t κ₂ c) ≡ subst H e₂ c) →
           ∀ (u₁ u₂ : H k → H t) → (∀ c → MoAt k c → u₁ c ≤ u₂ c) →
           hΩ κ₁ (λ c → u₁ (fr₁ c)) ≤ hΩ κ₂ (λ c → u₂ (fr₂ c))
  keepKK κ₁ κ₂ refl e₂ fr₁ fr₂ ft₁ ft₂ u₁ u₂ h =
    Ω≤Ω (sym e₂) (λ c mc → subst₂′ (ft₁ c) (trans (ft₂ (subst H (sym e₂) c)) (ssym e₂ c)) (h c (lmo→ t κ₁ c mc)))
    where
    ssym : ∀ {i j} (e : i ≡ j) (c : H j) → subst H e (subst H (sym e) c) ≡ c
    ssym refl c = refl
    subst₂′ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → u₁ a′ ≤ u₂ b′ → u₁ a ≤ u₂ b
    subst₂′ refl refl p = p

  keepMo : ∀ {k} (κ₁ : K (T t)) (e₁ : lvK t κ₁ ≡ k) (fr : E (T t) κ₁ → H k) →
           (∀ c → fr (toK t κ₁ c) ≡ subst H e₁ c) → ∀ (u : H k → H t) →
           (∀ c c′ → MoAt k c → MoAt k c′ → LeAt k c c′ → u c ≤ u c′) → (∀ c → MoAt k c → Mo (u c)) →
           Mo (hΩ κ₁ (λ c′ → u (fr c′)))
  keepMo κ₁ refl fr ft u um mu =
    (λ c c′ mc mc′ p → subst₂′ (ft c) (ft c′)
       (um c c′ (lmo→ t κ₁ c mc) (lmo→ t κ₁ c′ mc′) (lle→ t κ₁ c c′ p))) ,
    (λ c mc → subst (λ w → Mo (u w)) (sym (ft c)) (mu c (lmo→ t κ₁ c mc)))
    where
    subst₂′ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → u a′ ≤ u b′ → u a ≤ u b
    subst₂′ refl refl p = p
```

## §4 折叠: 记法, 输出不低于 1

`G a lm t pt b x`: 第 $m$ 层折到第 $t$ 层 (同底, 可数层号). `Kc`, `Sc`, `Ac`: $\Omega$-结点子句的三个续 (留 / 同层 / 在上), 与 `CRwFold.Φ` 的子句字面相同, 所以 `Φ … (hΩ κ g) tt` 就是 `caseDc (dcl pt lm (cl m κ)) (Kc …) (Sc …) (Ac …)`.

```agda
G : ∀ {m} → Acc b⊥ m → LgB m → ∀ t → t ⊲ m → H t → H m → H t
G {m} a lm t pt b x = Φ b⊥ m a lm b⊥ t (sm pt) b x tt

module _ {m : Cd} (rs : ∀ s′ i → Lt s′ i b⊥ m → Acc s′ i) (lm : LgB m) {κ : K (T m)} (g : E (T m) κ → H m) where
  Kc : ∀ {t} → t ⊲ m → H t → (κ′ : K (T t)) → (E (T t) κ′ → E (T m) κ) → H t
  Kc {t} pt b κ′ fr = hΩ κ′ (λ c → G (acc rs) lm t pt b (g (fr c)))
  Sc : ∀ {t} → t ⊲ m → H t → (H t → E (T m) κ) → H t
  Sc {t} pt b to = hl (chain b (λ b′ → G (acc rs) lm t pt b′ (g (to b′))))
  Ac : ∀ {t} → t ⊲ m → H t → (i : Cd) → hs i ⊲ m → t ⊲ i → (H i → E (T m) κ) → H t
  Ac {t} pt b i pi q to = G (rs b⊥ i (lt pi)) (lg↓ pi lm) t q b
    (hl (chain (top b⊥ i) (λ b′ → G (acc rs) lm i (⊏⊑ pi) b′ (g (to b′)))))

-- 把 Ω-结点子句的决定改写成 (层, 路径, 坐标) 的形式
ΦΩ : ∀ {m} rs lm {t} (pt : t ⊲ m) b κ (g : E (T m) κ → H m) (P : H t → Set) →
     P (caseDc (pick S⊥ (toK m κ) (pK m κ) (cmpB (pK m κ) pt tt lm)) (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b)) →
     P (G (acc rs) lm t pt b (hΩ κ g))
ΦΩ {m} rs lm pt b κ g P p =
  subst (λ cv → P (caseDc (dcl pt lm cv) (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))) (sym (clEq m κ)) p

caseP : ∀ {Lv : Cd → KS} {X t : Cd} {A R : Set} (P : R → Set) (d : Dc Lv X t A) {k s ab} →
        (∀ κ′ fr → P (k κ′ fr)) → (∀ to → P (s to)) → (∀ i u q to → P (ab i u q to)) → P (caseDc d k s ab)
caseP P (keep κ′ fr) pk ps pa = pk κ′ fr
caseP P (same to) pk ps pa = ps to
caseP P (above i u q to) pk ps pa = pa i u q to

one≤ : ∀ {m} a lm t pt b x → LeAt t (hs hz) (G {m} a lm t pt b x)
one≤ a lm t pt b hz = Rel.s≤s Rel.z≤
one≤ a lm t pt b (hs x) = Rel.≤l 0 (one≤ a lm t pt b x)
one≤ a lm t pt b (hl f) = Rel.≤l 0 (one≤ a lm t pt b (f 0))
one≤ {m} (acc rs) lm t pt b (hΩ κ g) = caseP (LeAt t (hs hz)) (dcl pt lm (cl m κ))
  (λ κ′ fr → Rel.≤Ω hz (LLe-z (lowT t) κ′ _) (LMo-z (lowT t) κ′) (one≤ (acc rs) lm t pt b (g (fr (toK t κ′ hz)))))
  (λ to → Rel.≤l 0 (one≤ (acc rs) lm t pt b (g (to b))))
  (λ i pi q to → one≤ (rs b⊥ i (lt pi)) (lg↓ pi lm) t q b
     (hl (chain (top b⊥ i) (λ b′ → G (acc rs) lm i (⊏⊑ pi) b′ (g (to b′))))))
```

## §5 决定只依赖层 (没有真回路)

`r` 是 `cmpB` 比较种类的位置 $k+1$ 与目标 $t$ 的结果. 留: `inj₂ q` 或 `inj₁ hself`; 同层: `inj₁ (hsuc hself)`; 在上: `inj₁ (hsuc q)`, $q$ 以后继或 ℕ-极限开头. 不同的路径给出同一类 (`nos`, `nl`).

```agda
-- 真第一位置 (在上的 q 的形状)
pp→⊲ : ∀ {t j} → Pp t j → t ⊲ j
pp→⊲ (pps u) = hsuc u
pp→⊲ (ppl n u) = hlim n u

s⊲→Pp : ∀ {k j} → hs k ⊲ j → Pp k j
s⊲→Pp hself = pps hself
s⊲→Pp (hsuc q) = pps (⊲ᴮ-tr (hsuc hself) q)
s⊲→Pp (hlim n q) = ppl n (⊲ᴮ-tr (hsuc hself) q)
s⊲→Pp (hLim {κ = ()} _ _)

Pp-tr : ∀ {a b c} → a ⊲ b → Pp b c → Pp a c
Pp-tr p (pps u) = pps (⊲ᴮ-tr p u)
Pp-tr p (ppl n u) = ppl n (⊲ᴮ-tr p u)

Pp→⊲ : ∀ {a c} → Pp a c → a ⊲ c
Pp→⊲ = pp→⊲

-- 真回路不存在的两种形状
noPP : ∀ {a b} → Pp a b → b ⊲ a → ⊥
noPP {a} pp q = nl a q pp
```

**层号上的结构可达性** `AP`: 对真第一位置 (`Pp`) 可达. 对一切可数层号成立 (`apWf`, 对层号结构递归). 下面的值定理在层号上对它归纳 (不用折叠自己的可达性证明, 那些只是数据).

```agda
data AP (k : Cd) : Set where
  ap : (∀ {j} → Pp j k → AP j) → AP k

apLe : ∀ {j k} → AP k → j ⊲ k → AP j
apLe a hself = a
apLe (ap h) (hsuc u) = apLe (h (pps hself)) u
apLe (ap h) (hlim n u) = apLe (h (ppl n hself)) u
apLe a (hLim {κ = ()} _ _)

apWf : ∀ k → AP k
apWf k = ap (λ pp → go k pp)
  where
  go : ∀ k {j} → Pp j k → AP j
  go (hs y) (pps u) = apLe (apWf y) u
  go (hl f) (ppl n u) = apLe (apWf (f n)) u
```

## 结论 (按档)

- **[定理]** 累加 `mul-mono`, `Mo-mul`, `≤mul`, `Mo-Σ`, `Σ-ge`, `Σ-idx`, `Σ-sub` (对严格增子列), `Σ-pt`, `mulΣ`; 链 `chM`, `chLe`, `chLe-hl`; 嵌入 `up-mono`, `Mo-up`, `ι-mono`, `Mo-ι`; **`Mo-top`** (一切地板值合法, 不要合法前提); 留下的结点 `keepR`, `keepKK`, `keepMo`; 折叠记法 `G`, `Kc`, `Sc`, `Ac`, `ΦΩ`, `caseP`; **`one≤`**; 真第一位置 `pp→⊲`, `s⊲→Pp`, `Pp-tr`, `noPP`; 层号的结构可达性 `AP`, `apLe`, `apWf`.
