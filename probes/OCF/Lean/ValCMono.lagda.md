# ValC (三): 同底折叠对世界与输入联合单调, 路线引理, 保值合法

> 不含记号. 入口 [ValC](ValC.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 只导入 stdlib, `OCF.Lean.CRw*`, [ValCRel](ValCRel.lagda.md), [ValCBase](ValCBase.lagda.md).
>
> **三条互递归的定理** (对一切 `I : CRwIf`; 可数层号 $m$, 目标 $t$; 可达性证明、合法证明、目标证据两边可以不同):
>
> - `monoΦ`: $x\le y$ (第 $m$ 层), 界 $b\le b'$ (第 $t$ 层, $\mathrm{top}\,t\le b$, 都值合法), $x, y$ 值合法 ⟹ $\Phi_{m\to t,b}\,x\le\Phi_{m\to t,b'}\,y$.
> - `route` (路线引理): 另有层号 $j$, 目标是 $j$ 的**真**第一位置 (`Pp t j`: 经后继或 ℕ-极限的一步之后才到 $t$) ⟹ $\Phi_{m\to t,b}\,x\le\Phi_{j\to t,b'}(\Phi_{m\to j,\mathrm{top}\,j}\,y)$.
> - `MoΦ`: 折叠保值合法.
>
> 归纳: 层号上对结构可达性 `AP` (`w : AP m`, 中间层 $j$ 的由 `Pp j m` 取出), 同一层上对左右输入的结构. 折叠的决定经视图 `DV` 读出 (留 / 同层 / 在上); 两边同一层的种类, 决定一致, 不一致的组合由没有真回路 (`nos`, `noPP`) 排除.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.ValCMono (I : CRwIf) (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Lean.ValCRel I
open import OCF.Lean.ValCBase I
```

## §1 Ω-结点的值合法读成层上的形式; 决定的视图

```agda
MoN : ∀ m k {κ} (to : H k → E (T m) κ) (g : E (T m) κ → H m) → Set
MoN m k to g = (∀ c c′ → MoAt k c → MoAt k c′ → LeAt k c c′ → LeAt m (g (to c)) (g (to c′))) ×
               (∀ c → MoAt k c → MoAt m (g (to c)))

moConv : ∀ {m κ} (g : E (T m) κ → H m) → MoAt m (hΩ κ g) → MoN m (lvK m κ) (toK m κ) g
moConv {m} {κ} g (mo , mh) =
  (λ c c′ mc mc′ p → mo c c′ (→lmo m κ c mc) (→lmo m κ c′ mc′) (→lle m κ c c′ p)) ,
  (λ c mc → mh c (→lmo m κ c mc))

data DV {m : Cd} {A : Set} : (k t : Cd) → (H k → A) → hs k ⊲ m → Dc (Tw S⊥) m t A → Set where
  dk : ∀ {k t to pk} (κ₁ : K (T t)) (e₁ : lvK t κ₁ ≡ k) (fr : E (T t) κ₁ → H k) →
       (∀ c → fr (toK t κ₁ c) ≡ subst H e₁ c) → hs k ⊲ t → DV k t to pk (keep κ₁ (λ c → to (fr c)))
  ds : ∀ {k to pk} → DV k k to pk (same to)
  da : ∀ {k t to pk} (q : t ⊲ k) → Pp t k → DV k t to pk (above k pk q to)

dv : ∀ {m A k t} (to : H k → A) (pk : hs k ⊲ m) (r : (t ⊲ hs k) ⊎ (hs k ⊲ t)) → DV k t to pk (pick S⊥ to pk r)
dv to pk (inj₂ q) = dk (along q) (lvA q) (frA q) (frto q) q
dv to pk (inj₁ hself) = dk (inj₂ tt) refl (λ c → c) (λ c → refl) hself
dv to pk (inj₁ (hsuc hself)) = ds
dv to pk (inj₁ (hsuc (hsuc q))) = da (hsuc q) (pps q)
dv to pk (inj₁ (hsuc (hlim n q))) = da (hlim n q) (ppl n q)
dv to pk (inj₁ (hsuc (hLim {κ = ()} _ _)))

dvK : ∀ {m} (κ : K (T m)) {t} (pt : t ⊲ m) (lm : LgB m) →
      DV (lvK m κ) t (toK m κ) (pK m κ) (pick S⊥ (toK m κ) (pK m κ) (cmpB (pK m κ) pt tt lm))
dvK {m} κ pt lm = dv (toK m κ) (pK m κ) (cmpB (pK m κ) pt tt lm)

ch : ∀ {m} (a : Acc b⊥ m) (lm : LgB m) {k} (pe : k ⊲ m) {κ} (g : E (T m) κ → H m) (to : H k → E (T m) κ) → H k → H k
ch a lm {k} pe g to b₁ = G a lm k pe b₁ (g (to b₁))
```

**两次 "同层" 的决定 (用到 Cd 上的 UIP).** 一边的决定已经是同层 ($t$ 与 $k$ 由合一等同) 时, 另一边的 `cmpB` 结果是 `inj₁ (hsuc r₂)`, $r_2 : k\lhd k$. 要 `pick` 化简成 `same`, 须 $r_2$ 字面是 `hself`; `--without-K` 下对它作模式匹配要消去自反方程 $k = k$ (第一次合一之后的第二次). 这里用 Cd 上的 UIP (模块参数 `uipC`) 证 $r_2\equiv$ `hself` (`selfLoop`): 非 `hself` 的情形是真回路, 由 `nos`, `nl` 排除. `uipC` 由函数外延推出 (`ValCUip.fe→uipC`, 条件).

```agda
selfLoop : ∀ {k : Cd} (r : k ⊲ k) → r ≡ hself
selfLoop r = lem r refl
  where
  lem : ∀ {t k : Cd} (r : t ⊲ k) (e : t ≡ k) → subst (λ z → z ⊲ k) e r ≡ hself
  lem {k = k} hself e = cong (λ e′ → subst (λ z → z ⊲ k) e′ hself) (uipC e refl)
  lem (hsuc r′) e = ⊥-elim (nos (subst (λ z → z ⊲ _) e r′))
  lem (hlim n r′) e = ⊥-elim (nl _ hself (ppl n (subst (λ z → z ⊲ _) e r′)))
  lem (hLim {κ = ()} _ _) e

sameR : ∀ {m A k} (to : H k → A) (pk : hs k ⊲ m) (r : (k ⊲ hs k) ⊎ (hs k ⊲ k)) → pick S⊥ to pk r ≡ same to
sameR to pk (inj₂ q) = ⊥-elim (nos q)
sameR to pk (inj₁ (hsuc r₂)) = cong (λ z → pick S⊥ to pk (inj₁ (hsuc z))) (selfLoop r₂)
```

## §2 三条互递归的定理

```agda
mutual
  monoΦ : ∀ {m} (w : AP m) (a a′ : Acc b⊥ m) (lm lm′ : LgB m) {t} (pt pt′ : t ⊲ m) {b b′} →
          Ac0.Bnd t b b′ → ∀ {x} y → MoAt m x → MoAt m y → LeAt m x y →
          LeAt t (G a lm t pt b x) (G a′ lm′ t pt′ b′ y)
  monoΦ w a a′ lm lm′ {t} pt pt′ B y mx my Rel.z≤ = one≤ a′ lm′ t pt′ _ y
  monoΦ w a a′ lm lm′ {t} pt pt′ B {hs x} (hs y) mx my (Rel.s≤s p) =
    Rel.l≤l (λ n → n) (L.idInc t) (Ac0.mul-mono t (monoΦ w a a′ lm lm′ pt pt′ B y mx my p))
  monoΦ w a a′ lm lm′ {t} pt pt′ B (hs y) mx my (Rel.≤s p) =
    Rel.≤l 0 (monoΦ w a a′ lm lm′ pt pt′ B y mx my p)
  monoΦ w a a′ lm lm′ {t} pt pt′ B {hl f} (hl g) mx my (Rel.l≤l σ i h) =
    Rel.l≤l σ i (Ac0.Σ-sub t _ _ σ i (λ n → monoΦ w a a′ lm lm′ pt pt′ B (g (σ n)) (mx n) (my (σ n)) (h n)))
  monoΦ w a a′ lm lm′ {t} pt pt′ B (hl g) mx my (Rel.≤l n p) =
    Rel.≤l n (L.≤-trans t (monoΦ w a a′ lm lm′ pt pt′ B (g n) mx (my n) p) (Ac0.Σ-ge t _ n))
  monoΦ {m} w a (acc rs′) lm lm′ {t} pt pt′ {b} {b′} B {x} (hΩ κ g) mx my (Rel.≤Ω c bd mc p) =
    ΦΩ rs′ lm′ pt′ b′ κ g (λ z → LeAt t (G a lm t pt b x) z)
      (mΩ1 w a rs′ lm lm′ pt pt′ B g (pK m κ) (toK m κ) (dvK κ pt′ lm′) mx (moConv g my)
         c (lle→ m κ c _ bd) (lmo→ m κ c mc) p)
  monoΦ {m} w (acc rs) (acc rs′) lm lm′ {t} pt pt′ {b} {b′} B {hΩ κ g} (hΩ κ′ g′) mx my (Rel.Ω≤Ω e h) =
    ΦΩ rs lm pt b κ g (λ z → LeAt t z (G (acc rs′) lm′ t pt′ b′ (hΩ κ′ g′)))
      (ΦΩ rs′ lm′ pt′ b′ κ′ g′
        (λ z → LeAt t (caseDc (pick S⊥ (toK m κ) (pK m κ) (cmpB (pK m κ) pt tt lm)) (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b)) z)
        (mΩΩe w rs rs′ lm lm′ pt pt′ B g g′ (pK m κ) (pK m κ′) (toK m κ) (toK m κ′) e
           (dvK κ pt lm) (cmpB (pK m κ′) pt′ tt lm′) (moConv g mx) (moConv g′ my) (λ c mc → h c (→lmo m κ c mc))))
```

**`≤Ω` 的三种决定.** 留: 在搬运后的坐标处取一支. 同层: 经 $c\le\mathrm{top}\,t\le b\le b'$ 与分支单调落到链的第 0 点. 在上: 路线引理接到 "经第 $k$ 层", 再用第 $k$ 层的单调 (层号下降).

```agda
  mΩ1 : ∀ {m} (w : AP m) (a : Acc b⊥ m) rs′ (lm lm′ : LgB m) {t} (pt pt′ : t ⊲ m) {b b′} → Ac0.Bnd t b b′ →
        ∀ {x κ} (g : E (T m) κ → H m) {k} (pk : hs k ⊲ m) (to : H k → E (T m) κ) {d} → DV k t to pk d →
        MoAt m x → MoN m k to g → ∀ c → LeAt k c (top b⊥ k) → MoAt k c → LeAt m x (g (to c)) →
        LeAt t (G a lm t pt b x) (caseDc d (Kc rs′ lm′ g pt′ b′) (Sc rs′ lm′ g pt′ b′) (Ac rs′ lm′ g pt′ b′))
  mΩ1 w a rs′ lm lm′ {t} pt pt′ {b} {b′} B g pk to (dk κ₁ e₁ fr ft u) mx My c bd mc p =
    keepR t κ₁ e₁ fr ft (λ c′ → G (acc rs′) lm′ t pt′ b′ (g (to c′))) c bd mc
      (monoΦ w a (acc rs′) lm lm′ pt pt′ B (g (to c)) mx (proj₂ My c mc) p)
  mΩ1 {m} w a rs′ lm lm′ {t} pt pt′ {b} {b′} B@(mb , mb′ , tb , bb) g pk to ds mx My c bd mc p =
    Rel.≤l 0 (monoΦ w a (acc rs′) lm lm′ pt pt′ B (g (to b′)) mx (proj₂ My b′ mb′)
      (L.≤-trans m p (proj₁ My c b′ mc mb′ (L.≤-trans t bd (L.≤-trans t tb bb)))))
  mΩ1 {m} (ap hw) a rs′ lm lm′ {t} pt pt′ {b} {b′} B@(mb , mb′ , tb , bb) g {k} pk to (da q pp) mx My c bd mc p =
    L.≤-trans t
      (route (ap hw) (s⊲→Pp pk) a (acc rs′) lm lm′ (rs′ b⊥ k (lt pk)) (lg↓ pk lm′) (⊏⊑ pk) pt q pp B (g (to c)) mx (proj₂ My c mc) p)
      (monoΦ (hw (s⊲→Pp pk)) (rs′ b⊥ k (lt pk)) (rs′ b⊥ k (lt pk)) (lg↓ pk lm′) (lg↓ pk lm′) q q
         (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (hl (chain (top b⊥ k) (ch (acc rs′) lm′ (⊏⊑ pk) g to)))
         (MoΦ (ap hw) (acc rs′) lm′ (⊏⊑ pk) (Mo-top k) (L.≤-refl k _) (g (to c)) (proj₂ My c mc))
         (moCh (ap hw) (acc rs′) lm′ (⊏⊑ pk) g to My)
         (Rel.≤l 0 (monoΦ (ap hw) (acc rs′) (acc rs′) lm′ lm′ (⊏⊑ pk) (⊏⊑ pk)
            (Ac0.bnd-refl k (Mo-top k) (L.≤-refl k _)) (g (to (top b⊥ k)))
            (proj₂ My c mc) (proj₂ My _ (Mo-top k)) (proj₁ My c _ mc (Mo-top k) bd))))
```

**`Ω≤Ω`**: 两边同一层 $k$ ($e$ 先用 J 消去); 决定一致.

```agda
  mΩΩe : ∀ {m} (w : AP m) rs rs′ (lm lm′ : LgB m) {t} (pt pt′ : t ⊲ m) {b b′} → Ac0.Bnd t b b′ →
         ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k k′} (pk : hs k ⊲ m) (pk′ : hs k′ ⊲ m)
         (to : H k → E (T m) κ) (to′ : H k′ → E (T m) κ′) (e : k ≡ k′) {d} →
         DV k t to pk d → (r′ : (t ⊲ hs k′) ⊎ (hs k′ ⊲ t)) → MoN m k to g → MoN m k′ to′ g′ →
         (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ (subst H e c)))) →
         LeAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
                (caseDc (pick S⊥ to′ pk′ r′) (Kc rs′ lm′ g′ pt′ b′) (Sc rs′ lm′ g′ pt′ b′) (Ac rs′ lm′ g′ pt′ b′))
  mΩΩe w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ refl D r′ Mx My H′ =
    mΩΩ w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ D r′ Mx My H′

  mΩΩ : ∀ {m} (w : AP m) rs rs′ (lm lm′ : LgB m) {t} (pt pt′ : t ⊲ m) {b b′} → Ac0.Bnd t b b′ →
        ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk pk′ : hs k ⊲ m)
        (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) {d} →
        DV k t to pk d → (r′ : (t ⊲ hs k) ⊎ (hs k ⊲ t)) → MoN m k to g → MoN m k to′ g′ →
        (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
        LeAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
               (caseDc (pick S⊥ to′ pk′ r′) (Kc rs′ lm′ g′ pt′ b′) (Sc rs′ lm′ g′ pt′ b′) (Ac rs′ lm′ g′ pt′ b′))
  mΩΩ w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ (dk κ₁ e₁ fr₁ ft₁ u₁) r′ Mx My H′ =
    mΩΩk w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ κ₁ e₁ fr₁ ft₁ u₁ (dv to′ pk′ r′) Mx My H′
  mΩΩ {m} w rs rs′ lm lm′ {t} pt pt′ {b} {b′} B g g′ pk pk′ to to′ ds r′ Mx My H′ =
    subst (λ z → LeAt t (Sc rs lm g pt b to) (caseDc z (Kc rs′ lm′ g′ pt′ b′) (Sc rs′ lm′ g′ pt′ b′) (Ac rs′ lm′ g′ pt′ b′)))
      (sym (sameR to′ pk′ r′))
      (Ac0.chLe-hl t (ch (acc rs) lm pt g to) (ch (acc rs′) lm′ pt′ g′ to′) B
        (kpG w (acc rs) lm pt g to Mx) (kpG w (acc rs′) lm′ pt′ g′ to′ My)
        (chCmp w (acc rs) (acc rs′) lm lm′ pt pt′ g g′ to to′ Mx My H′))
  mΩΩ w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ (da q pp) r′ Mx My H′ =
    mΩΩa w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ q pp (dv to′ pk′ r′) Mx My H′

  mΩΩk : ∀ {m} (w : AP m) rs rs′ (lm lm′ : LgB m) {t} (pt pt′ : t ⊲ m) {b b′} → Ac0.Bnd t b b′ →
         ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk pk′ : hs k ⊲ m)
         (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) (κ₁ : K (T t)) (e₁ : lvK t κ₁ ≡ k) (fr₁ : E (T t) κ₁ → H k) →
         (∀ c → fr₁ (toK t κ₁ c) ≡ subst H e₁ c) → hs k ⊲ t → ∀ {d′} → DV k t to′ pk′ d′ →
         MoN m k to g → MoN m k to′ g′ → (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
         LeAt t (Kc rs lm g pt b κ₁ (λ c → to (fr₁ c)))
                (caseDc d′ (Kc rs′ lm′ g′ pt′ b′) (Sc rs′ lm′ g′ pt′ b′) (Ac rs′ lm′ g′ pt′ b′))
  mΩΩk w rs rs′ lm lm′ {t} pt pt′ {b} {b′} B g g′ pk pk′ to to′ κ₁ e₁ fr₁ ft₁ u₁ (dk κ₂ e₂ fr₂ ft₂ u₂) Mx My H′ =
    keepKK t κ₁ κ₂ e₁ e₂ fr₁ fr₂ ft₁ ft₂ (λ c → G (acc rs) lm t pt b (g (to c))) (λ c → G (acc rs′) lm′ t pt′ b′ (g′ (to′ c)))
      (λ c mc → monoΦ w (acc rs) (acc rs′) lm lm′ pt pt′ B (g′ (to′ c)) (proj₂ Mx c mc) (proj₂ My c mc) (H′ c mc))
  mΩΩk w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ κ₁ e₁ fr₁ ft₁ u₁ ds Mx My H′ = ⊥-elim (nos u₁)
  mΩΩk w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ κ₁ e₁ fr₁ ft₁ u₁ (da q pp) Mx My H′ = ⊥-elim (nos′ u₁ q)

  mΩΩa : ∀ {m} (w : AP m) rs rs′ (lm lm′ : LgB m) {t} (pt pt′ : t ⊲ m) {b b′} → Ac0.Bnd t b b′ →
         ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk pk′ : hs k ⊲ m)
         (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) (q : t ⊲ k) → Pp t k → ∀ {d′} → DV k t to′ pk′ d′ →
         MoN m k to g → MoN m k to′ g′ → (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
         LeAt t (Ac rs lm g pt b k pk q to)
                (caseDc d′ (Kc rs′ lm′ g′ pt′ b′) (Sc rs′ lm′ g′ pt′ b′) (Ac rs′ lm′ g′ pt′ b′))
  mΩΩa w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ q pp (dk κ₂ e₂ fr₂ ft₂ u₂) Mx My H′ = ⊥-elim (nos′ u₂ q)
  mΩΩa w rs rs′ lm lm′ pt pt′ B g g′ pk pk′ to to′ q pp ds Mx My H′ = ⊥-elim (noPP pp hself)
  mΩΩa {m} (ap hw) rs rs′ lm lm′ {t} pt pt′ {b} {b′} B g g′ {k} pk pk′ to to′ q pp (da q′ pp′) Mx My H′ =
    monoΦ (hw (s⊲→Pp pk)) (rs b⊥ k (lt pk)) (rs′ b⊥ k (lt pk′)) (lg↓ pk lm) (lg↓ pk′ lm′) q q′ B
      (hl (chain (top b⊥ k) (ch (acc rs′) lm′ (⊏⊑ pk′) g′ to′)))
      (moCh (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx) (moCh (ap hw) (acc rs′) lm′ (⊏⊑ pk′) g′ to′ My)
      (Ac0.chLe-hl k (ch (acc rs) lm (⊏⊑ pk) g to) (ch (acc rs′) lm′ (⊏⊑ pk′) g′ to′)
         (Ac0.bnd-refl k (Mo-top k) (L.≤-refl k _))
         (kpG (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx) (kpG (ap hw) (acc rs′) lm′ (⊏⊑ pk′) g′ to′ My)
         (chCmp (ap hw) (acc rs) (acc rs′) lm lm′ (⊏⊑ pk) (⊏⊑ pk′) g g′ to to′ Mx My H′))
```

**链的三个小件**: 链点值合法 (`kpG`), 整条链值合法 (`moCh`), 两条链逐点比较 (`chCmp`).

```agda
  kpG : ∀ {m} (w : AP m) (a : Acc b⊥ m) (lm : LgB m) {k} (pe : k ⊲ m) {κ} (g : E (T m) κ → H m) (to : H k → E (T m) κ) →
        MoN m k to g → Ac0.KP k (ch a lm pe g to)
  kpG w a lm pe g to Mx b₁ mb tb = MoΦ w a lm pe mb tb (g (to b₁)) (proj₂ Mx b₁ mb)

  moCh : ∀ {m} (w : AP m) (a : Acc b⊥ m) (lm : LgB m) {k} (pe : k ⊲ m) {κ} (g : E (T m) κ → H m) (to : H k → E (T m) κ) →
         MoN m k to g → MoAt k (hl (chain (top b⊥ k) (ch a lm pe g to)))
  moCh w a lm {k} pe g to Mx = Ac0.chM k (top b⊥ k) _ (Mo-top k) (L.≤-refl k _) (kpG w a lm pe g to Mx)

  chCmp : ∀ {m} (w : AP m) (a a′ : Acc b⊥ m) (lm lm′ : LgB m) {k} (pe pe′ : k ⊲ m) {κ κ′}
          (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) →
          MoN m k to g → MoN m k to′ g′ → (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
          ∀ {b₁ b₂} → Ac0.Bnd k b₁ b₂ → LeAt k (ch a lm pe g to b₁) (ch a′ lm′ pe′ g′ to′ b₂)
  chCmp {m} w a a′ lm lm′ pe pe′ g g′ to to′ Mx My H′ {b₁} {b₂} B₁@(m1 , m2 , t1 , le) =
    monoΦ w a a′ lm lm′ pe pe′ B₁ (g′ (to′ b₂)) (proj₂ Mx b₁ m1) (proj₂ My b₂ m2)
      (L.≤-trans m (H′ b₁ m1) (proj₁ My b₁ b₂ m1 m2 le))
```

**保值合法.**

```agda
  MoΦ : ∀ {m} (w : AP m) (a : Acc b⊥ m) (lm : LgB m) {t} (pt : t ⊲ m) {b} →
        MoAt t b → LeAt t (top b⊥ t) b → ∀ x → MoAt m x → MoAt t (G a lm t pt b x)
  MoΦ w a lm pt mb tb hz mx = tt
  MoΦ w a lm {t} pt mb tb (hs x) mx = Ac0.Mo-mul t _ (MoΦ w a lm pt mb tb x mx)
  MoΦ w a lm {t} pt mb tb (hl f) mx = Ac0.Mo-Σ t _ (λ n → MoΦ w a lm pt mb tb (f n) (mx n))
  MoΦ {m} w (acc rs) lm {t} pt {b} mb tb (hΩ κ g) mx =
    ΦΩ rs lm pt b κ g (MoAt t) (moΩ w rs lm pt mb tb g (pK m κ) (toK m κ) (dvK κ pt lm) (moConv g mx))

  moΩ : ∀ {m} (w : AP m) rs (lm : LgB m) {t} (pt : t ⊲ m) {b} → MoAt t b → LeAt t (top b⊥ t) b →
        ∀ {κ} (g : E (T m) κ → H m) {k} (pk : hs k ⊲ m) (to : H k → E (T m) κ) {d} → DV k t to pk d → MoN m k to g →
        MoAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
  moΩ w rs lm {t} pt {b} mb tb g pk to (dk κ₁ e₁ fr ft u) Mx =
    keepMo t κ₁ e₁ fr ft (λ c → G (acc rs) lm t pt b (g (to c)))
      (λ c c′ mc mc′ p → monoΦ w (acc rs) (acc rs) lm lm pt pt (Ac0.bnd-refl t mb tb) (g (to c′))
         (proj₂ Mx c mc) (proj₂ Mx c′ mc′) (proj₁ Mx c c′ mc mc′ p))
      (λ c mc → MoΦ w (acc rs) lm pt mb tb (g (to c)) (proj₂ Mx c mc))
  moΩ w rs lm {t} pt {b} mb tb g pk to ds Mx = Ac0.chM t b _ mb tb (kpG w (acc rs) lm pt g to Mx)
  moΩ (ap hw) rs lm {t} pt {b} mb tb g {k} pk to (da q pp) Mx =
    MoΦ (hw (s⊲→Pp pk)) (rs b⊥ k (lt pk)) (lg↓ pk lm) q mb tb (hl (chain (top b⊥ k) (ch (acc rs) lm (⊏⊑ pk) g to)))
      (moCh (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx)
```

**路线引理.** 对 $x\le y$ 的推导. 后继、ℕ-极限: 右边的两步折叠先在第 $j$ 层做部分积 / 部分和, 再折到 $t$; 用第 $j$ 层的单调把它们接上. `≤Ω`: 归纳假设接到 $y$ 的一支, 再用第 $m$ 层到第 $j$ 层的单调 (同一个 $y$) 与第 $j$ 层的单调. `Ω≤Ω`: 按 "种类的层 $k$ 对 $j$ 的决定" 分三种 (留 / 同层 / 在上), 再对左边 ($k$ 对 $t$) 与右边第二步 ($k$ 对 $t$) 的决定.

```agda
  route : ∀ {m j} (w : AP m) (pjP : Pp j m) (a a″ : Acc b⊥ m) (lm lm″ : LgB m) (aj : Acc b⊥ j) (lj : LgB j)
          (pjm : j ⊲ m) {t} (pt : t ⊲ m) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
          ∀ {x} y → MoAt m x → MoAt m y → LeAt m x y →
          LeAt t (G a lm t pt b x) (G aj lj t qo b′ (G a″ lm″ j pjm (top b⊥ j) y))
  route w pjP a a″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B y mx my Rel.z≤ =
    one≤ aj lj t qo b′ (G a″ lm″ _ pjm (top b⊥ _) y)
  route {m} {j} w@(ap hw) pjP a a″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B@(mb , mb′ , tb , bb) {hs x} (hs y) mx my (Rel.s≤s p) =
    Rel.l≤l (λ n → n) (L.idInc t) (λ n → L.≤-trans t
      (Ac0.mul-mono t (route w pjP a a″ lm lm″ aj lj pjm pt qo pp B y mx my p) n)
      (Ac0.mulΣ t (G aj lj t qo b′ (G a″ lm″ j pjm (top b⊥ j) y)) (λ k → G aj lj t qo b′ (mul (G a″ lm″ j pjm (top b⊥ j) y) k))
         (λ k → monoΦ (hw pjP) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (mul (G a″ lm″ j pjm (top b⊥ j) y) k)
            (MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) y my)
            (Ac0.Mo-mul j _ (MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) y my) k)
            (Ac0.≤mul j _ k)) n))
  route w pjP a a″ lm lm″ aj lj pjm {t} pt qo pp B (hs y) mx my (Rel.≤s p) =
    Rel.≤l 0 (route w pjP a a″ lm lm″ aj lj pjm pt qo pp B y mx my p)
  route {m} {j} w@(ap hw) pjP a a″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B@(mb , mb′ , tb , bb) {hl f} (hl g) mx my (Rel.l≤l σ i h) =
    Rel.l≤l σ i (Ac0.Σ-sub t _ _ σ i (λ n → L.≤-trans t
      (route w pjP a a″ lm lm″ aj lj pjm pt qo pp B (g (σ n)) (mx n) (my (σ n)) (h n))
      (monoΦ (hw pjP) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (Σ⁺ (λ k → G a″ lm″ j pjm (top b⊥ j) (g k)) (σ n))
         (MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) (g (σ n)) (my (σ n)))
         (Ac0.Mo-Σ j _ (λ k → MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) (g k) (my k)) (σ n))
         (Ac0.Σ-ge j (λ k → G a″ lm″ j pjm (top b⊥ j) (g k)) (σ n)))))
  route {m} {j} w@(ap hw) pjP a a″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B@(mb , mb′ , tb , bb) (hl g) mx my (Rel.≤l n p) =
    Rel.≤l n (L.≤-trans t (route w pjP a a″ lm lm″ aj lj pjm pt qo pp B (g n) mx (my n) p)
      (L.≤-trans t (monoΦ (hw pjP) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (Σ⁺ (λ k → G a″ lm″ j pjm (top b⊥ j) (g k)) n)
           (MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) (g n) (my n))
           (Ac0.Mo-Σ j _ (λ k → MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) (g k) (my k)) n)
           (Ac0.Σ-ge j (λ k → G a″ lm″ j pjm (top b⊥ j) (g k)) n))
        (Ac0.Σ-ge t _ n)))
  route {m} {j} w@(ap hw) pjP a a″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B@(mb , mb′ , tb , bb) (hΩ κ g) mx my (Rel.≤Ω c bd mc p) =
    L.≤-trans t (route w pjP a a″ lm lm″ aj lj pjm pt qo pp B (g (toK m κ c)) mx (proj₂ my c mc) p)
      (monoΦ (hw pjP) aj aj lj lj qo qo (Ac0.bnd-refl t mb′ (L.≤-trans t tb bb)) (G a″ lm″ j pjm (top b⊥ j) (hΩ κ g))
         (MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) (g (toK m κ c)) (proj₂ my c mc))
         (MoΦ w a″ lm″ pjm (Mo-top j) (L.≤-refl j _) (hΩ κ g) my)
         (monoΦ w a″ a″ lm″ lm″ pjm pjm (Ac0.bnd-refl j (Mo-top j) (L.≤-refl j _)) (hΩ κ g)
            (proj₂ my c mc) my (Rel.≤Ω c bd mc (L.≤-refl m _))))
  route {m} {j} w@(ap hw) pjP (acc rs) (acc rs″) lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B {hΩ κ g} (hΩ κ′ g′) mx my (Rel.Ω≤Ω e h) =
    ΦΩ rs lm pt b κ g (λ z → LeAt t z (G aj lj t qo b′ (G (acc rs″) lm″ j pjm (top b⊥ j) (hΩ κ′ g′))))
      (ΦΩ rs″ lm″ pjm (top b⊥ j) κ′ g′
        (λ z → LeAt t (caseDc (pick S⊥ (toK m κ) (pK m κ) (cmpB (pK m κ) pt tt lm)) (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
                      (G aj lj t qo b′ z))
        (rΩΩe w (hw pjP) pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ (pK m κ) (pK m κ′) (toK m κ) (toK m κ′) e
           (dvK κ pt lm) (dvK κ′ pjm lm″) (moConv g mx) (moConv g′ my) (λ c mc → h c (→lmo m κ c mc))))
```

**路线引理的 `Ω≤Ω`.** 先消去 $e$; 再按第一步 (第 $m$ 层折到第 $j$ 层) 的决定.

```agda
  rΩΩe : ∀ {m j} (w : AP m) (wj : AP j) (pjP : Pp j m) rs rs″ (lm lm″ : LgB m) (aj : Acc b⊥ j) (lj : LgB j)
         (pjm : j ⊲ m) {t} (pt : t ⊲ m) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
         ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k k′} (pk : hs k ⊲ m) (pk′ : hs k′ ⊲ m)
         (to : H k → E (T m) κ) (to′ : H k′ → E (T m) κ′) (e : k ≡ k′) {d d″} →
         DV k t to pk d → DV k′ j to′ pk′ d″ → MoN m k to g → MoN m k′ to′ g′ →
         (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ (subst H e c)))) →
         LeAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
                (G aj lj t qo b′ (caseDc d″ (Kc rs″ lm″ g′ pjm (top b⊥ j)) (Sc rs″ lm″ g′ pjm (top b⊥ j)) (Ac rs″ lm″ g′ pjm (top b⊥ j))))
  rΩΩe w wj pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ pk pk′ to to′ refl D D″ Mx My H′ =
    rΩΩ w wj pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ pk pk′ to to′ D D″ Mx My H′

  rΩΩ : ∀ {m j} (w : AP m) (wj : AP j) (pjP : Pp j m) rs rs″ (lm lm″ : LgB m) (aj : Acc b⊥ j) (lj : LgB j)
        (pjm : j ⊲ m) {t} (pt : t ⊲ m) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
        ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk pk′ : hs k ⊲ m)
        (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) {d d″} →
        DV k t to pk d → DV k j to′ pk′ d″ → MoN m k to g → MoN m k to′ g′ →
        (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
        LeAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
               (G aj lj t qo b′ (caseDc d″ (Kc rs″ lm″ g′ pjm (top b⊥ j)) (Sc rs″ lm″ g′ pjm (top b⊥ j)) (Ac rs″ lm″ g′ pjm (top b⊥ j))))
  -- 第一步留下 (k < j)
  rΩΩ {m} {j} w wj pjP rs rs″ lm lm″ (acc rsj) lj pjm {t} pt qo pp {b} {b′} B g g′ pk pk′ to to′ {d} D (dk κ₁ e₁ fr₁ ft₁ u₁) Mx My H′ =
    ΦΩ rsj lj qo b′ κ₁ G1
      (λ z → LeAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b)) z)
      (rK w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ (s⊲→Pp u₁)
         (toK j κ₁) e₁ ft₁ (pK j κ₁) D (cmpB (pK j κ₁) qo tt lj) Mx My H′)
    where
    G1 : E (T j) κ₁ → H j
    G1 c = G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))
  -- 第一步同层 (k = j)
  rΩΩ w wj pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ pk pk′ to to′ (dk κ₁ e₁ fr₁ ft₁ u) ds Mx My H′ =
    ⊥-elim (nos′ u (pp→⊲ pp))
  rΩΩ w wj pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ pk pk′ to to′ ds ds Mx My H′ = ⊥-elim (noPP pp hself)
  rΩΩ {m} {j} w wj pjP rs rs″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B g g′ pk pk′ to to′ (da qL ppL) ds Mx My H′ =
    monoΦ wj (rs b⊥ j (lt pk)) aj (lg↓ pk lm) lj qL qo B
      (hl (chain (top b⊥ j) (ch (acc rs″) lm″ pjm g′ to′)))
      (moCh w (acc rs) lm (⊏⊑ pk) g to Mx) (moCh w (acc rs″) lm″ pjm g′ to′ My)
      (Ac0.chLe-hl j (ch (acc rs) lm (⊏⊑ pk) g to) (ch (acc rs″) lm″ pjm g′ to′)
         (Ac0.bnd-refl j (Mo-top j) (L.≤-refl j _))
         (kpG w (acc rs) lm (⊏⊑ pk) g to Mx) (kpG w (acc rs″) lm″ pjm g′ to′ My)
         (chCmp w (acc rs) (acc rs″) lm lm″ (⊏⊑ pk) pjm g g′ to to′ Mx My H′))
  -- 第一步在上 (j < k)
  rΩΩ w wj pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ pk pk′ to to′ (dk κ₁ e₁ fr₁ ft₁ u) (da q₁ pp₁) Mx My H′ =
    ⊥-elim (nos (⊲ᴮ-tr u (⊲ᴮ-tr (pp→⊲ pp) q₁)))
  rΩΩ w wj pjP rs rs″ lm lm″ aj lj pjm pt qo pp B g g′ pk pk′ to to′ ds (da q₁ pp₁) Mx My H′ = ⊥-elim (noPP pp q₁)
  rΩΩ {m} {j} (ap hw) wj pjP rs rs″ lm lm″ aj lj pjm {t} pt qo pp {b} {b′} B g g′ {k} pk pk′ to to′ (da qL ppL) (da q₁ pp₁) Mx My H′ =
    route (hw (s⊲→Pp pk)) pp₁ (rs b⊥ k (lt pk)) (rs″ b⊥ k (lt pk′)) (lg↓ pk lm) (lg↓ pk′ lm″) aj lj q₁ qL qo pp B
      (hl (chain (top b⊥ k) (ch (acc rs″) lm″ (⊏⊑ pk′) g′ to′)))
      (moCh (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx) (moCh (ap hw) (acc rs″) lm″ (⊏⊑ pk′) g′ to′ My)
      (Ac0.chLe-hl k (ch (acc rs) lm (⊏⊑ pk) g to) (ch (acc rs″) lm″ (⊏⊑ pk′) g′ to′)
         (Ac0.bnd-refl k (Mo-top k) (L.≤-refl k _))
         (kpG (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx) (kpG (ap hw) (acc rs″) lm″ (⊏⊑ pk′) g′ to′ My)
         (chCmp (ap hw) (acc rs) (acc rs″) lm lm″ (⊏⊑ pk) (⊏⊑ pk′) g g′ to to′ Mx My H′))
```

**第一步留下之后**: 留下的种类 $\kappa_1$ 在第 $j$ 层, 层也是 $k$; 第二步 (第 $j$ 层折到 $t$) 的决定与左边 ($m$ 折到 $t$) 的决定一致.

```agda
  rK : ∀ {m j} (w : AP m) (wj : AP j) (pjP : Pp j m) rs rs″ (lm lm″ : LgB m) rsj (lj : LgB j)
       (pjm : j ⊲ m) {t} (pt : t ⊲ m) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
       ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk : hs k ⊲ m)
       (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) (κ₁ : K (T j)) (fr₁ : E (T j) κ₁ → H k) → Pp k j →
       ∀ {k₁} (to₁ : H k₁ → E (T j) κ₁) (e₁ : k₁ ≡ k) → (∀ c → fr₁ (to₁ c) ≡ subst H e₁ c) → (pk₁ : hs k₁ ⊲ j) →
       ∀ {d} → DV k t to pk d → (r₁ : (t ⊲ hs k₁) ⊎ (hs k₁ ⊲ t)) → MoN m k to g → MoN m k to′ g′ →
       (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
       LeAt t (caseDc d (Kc rs lm g pt b) (Sc rs lm g pt b) (Ac rs lm g pt b))
              (caseDc (pick S⊥ to₁ pk₁ r₁) (Kc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′)
                         (Sc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′)
                         (Ac rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′))
  rK w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ refl ft pk₁ (dk κL eL frL ftL uL) r₁ Mx My H′ =
    rKk w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL (dv to₁ pk₁ r₁) Mx My H′
  rK {m} {j} w wj pjP rs rs″ lm lm″ rsj lj pjm {t} pt qo pp {b} {b′} B@(mb , mb′ , tb , bb) g g′ pk to to′ κ₁ fr₁ pkj to₁ refl ft pk₁ ds r₁ Mx My H′ =
    subst (λ z → LeAt t (Sc rs lm g pt b to) (caseDc z (Kc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′) (Sc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′) (Ac rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′)))
      (sym (sameR to₁ pk₁ r₁))
      (Ac0.chLe-hl t (ch (acc rs) lm pt g to) kR B (kpG w (acc rs) lm pt g to Mx)
        (λ b₂ m2 t2 → MoΦ wj (acc rsj) lj qo m2 t2 _
           (MoΦ w (acc rs″) lm″ pjm (Mo-top j) (L.≤-refl j _) _ (proj₂ My _ (subst (MoAt t) (sym (ft b₂)) m2))))
        (λ {b₁} {b₂} B₁@(m1 , m2 , t1 , le) →
           subst (λ z → LeAt t (G (acc rs) lm t pt b₁ (g (to b₁))) (G (acc rsj) lj t qo b₂ (G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ z)))))
             (sym (ft b₂))
             (route w pjP (acc rs) (acc rs″) lm lm″ (acc rsj) lj pjm pt qo pp B₁ (g′ (to′ b₂)) (proj₂ Mx b₁ m1) (proj₂ My b₂ m2)
                (L.≤-trans m (H′ b₁ m1) (proj₁ My b₁ b₂ m1 m2 le)))))
    where
    kR : H t → H t
    kR b₂ = G (acc rsj) lj t qo b₂ (G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ (to₁ b₂)))))
  rK w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ refl ft pk₁ (da qL ppL) r₁ Mx My H′ =
    rKa w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ qL ppL (dv to₁ pk₁ r₁) Mx My H′

  rKk : ∀ {m j} (w : AP m) (wj : AP j) (pjP : Pp j m) rs rs″ (lm lm″ : LgB m) rsj (lj : LgB j)
        (pjm : j ⊲ m) {t} (pt : t ⊲ m) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
        ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk : hs k ⊲ m)
        (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) (κ₁ : K (T j)) (fr₁ : E (T j) κ₁ → H k) → Pp k j →
        (to₁ : H k → E (T j) κ₁) → (∀ c → fr₁ (to₁ c) ≡ c) → (pk₁ : hs k ⊲ j) →
        (κL : K (T t)) (eL : lvK t κL ≡ k) (frL : E (T t) κL → H k) → (∀ c → frL (toK t κL c) ≡ subst H eL c) → hs k ⊲ t →
        ∀ {d₁} → DV k t to₁ pk₁ d₁ → MoN m k to g → MoN m k to′ g′ →
        (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
        LeAt t (Kc rs lm g pt b κL (λ c → to (frL c))) (caseDc d₁ (Kc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′) (Sc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′) (Ac rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′))
  rKk {m} {j} w wj pjP rs rs″ lm lm″ rsj lj pjm {t} pt qo pp {b} {b′} B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL
     (dk κR eR frR ftR uR) Mx My H′ =
    keepKK t κL κR eL eR frL frR ftL ftR (λ c → G (acc rs) lm t pt b (g (to c)))
      (λ c → G (acc rsj) lj t qo b′ (G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ (to₁ c))))))
      (λ c mc → subst (λ z → LeAt t (G (acc rs) lm t pt b (g (to c))) (G (acc rsj) lj t qo b′ (G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ z)))))
         (sym (ft c))
         (route w pjP (acc rs) (acc rs″) lm lm″ (acc rsj) lj pjm pt qo pp B (g′ (to′ c)) (proj₂ Mx c mc) (proj₂ My c mc) (H′ c mc)))
  rKk w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL ds Mx My H′ =
    ⊥-elim (nos uL)
  rKk w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ κL eL frL ftL uL (da q pq) Mx My H′ =
    ⊥-elim (nos′ uL q)

  rKa : ∀ {m j} (w : AP m) (wj : AP j) (pjP : Pp j m) rs rs″ (lm lm″ : LgB m) rsj (lj : LgB j)
        (pjm : j ⊲ m) {t} (pt : t ⊲ m) (qo : t ⊲ j) (pp : Pp t j) {b b′} → Ac0.Bnd t b b′ →
        ∀ {κ κ′} (g : E (T m) κ → H m) (g′ : E (T m) κ′ → H m) {k} (pk : hs k ⊲ m)
        (to : H k → E (T m) κ) (to′ : H k → E (T m) κ′) (κ₁ : K (T j)) (fr₁ : E (T j) κ₁ → H k) → Pp k j →
        (to₁ : H k → E (T j) κ₁) → (∀ c → fr₁ (to₁ c) ≡ c) → (pk₁ : hs k ⊲ j) →
        (qL : t ⊲ k) → Pp t k →
        ∀ {d₁} → DV k t to₁ pk₁ d₁ → MoN m k to g → MoN m k to′ g′ →
        (∀ c → MoAt k c → LeAt m (g (to c)) (g′ (to′ c))) →
        LeAt t (Ac rs lm g pt b k pk qL to) (caseDc d₁ (Kc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′) (Sc rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′) (Ac rsj lj (λ c → G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ c)))) qo b′))
  rKa w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ qL ppL (dk κR eR frR ftR uR) Mx My H′ =
    ⊥-elim (nos′ uR qL)
  rKa w wj pjP rs rs″ lm lm″ rsj lj pjm pt qo pp B g g′ pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ qL ppL ds Mx My H′ =
    ⊥-elim (noPP ppL hself)
  rKa {m} {j} (ap hw) wj pjP rs rs″ lm lm″ rsj lj pjm {t} pt qo pp {b} {b′} B g g′ {k} pk to to′ κ₁ fr₁ pkj to₁ ft pk₁ qL ppL
     (da qR ppR) Mx My H′ =
    monoΦ (hw (s⊲→Pp pk)) (rs b⊥ k (lt pk)) (rsj b⊥ k (lt pk₁)) (lg↓ pk lm) (lg↓ pk₁ lj) qL qR B
      (hl (chain (top b⊥ k) kR))
      (moCh (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx)
      (Ac0.chM k (top b⊥ k) kR (Mo-top k) (L.≤-refl k _) (λ b₂ m2 t2 → MoΦ wj (acc rsj) lj (⊏⊑ pk₁) m2 t2 _
           (MoΦ (ap hw) (acc rs″) lm″ pjm (Mo-top j) (L.≤-refl j _) _ (proj₂ My _ (subst (MoAt k) (sym (ft b₂)) m2)))))
      (Ac0.chLe-hl k (ch (acc rs) lm (⊏⊑ pk) g to) kR (Ac0.bnd-refl k (Mo-top k) (L.≤-refl k _))
         (kpG (ap hw) (acc rs) lm (⊏⊑ pk) g to Mx) (λ b₂ m2 t2 → MoΦ wj (acc rsj) lj (⊏⊑ pk₁) m2 t2 _
           (MoΦ (ap hw) (acc rs″) lm″ pjm (Mo-top j) (L.≤-refl j _) _ (proj₂ My _ (subst (MoAt k) (sym (ft b₂)) m2))))
         (λ {b₁} {b₂} B₁@(m1 , m2 , t1 , le) →
            subst (λ z → LeAt k (G (acc rs) lm k (⊏⊑ pk) b₁ (g (to b₁)))
                                (G (acc rsj) lj k (⊏⊑ pk₁) b₂ (G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ z)))))
              (sym (ft b₂))
              (route (ap hw) pjP (acc rs) (acc rs″) lm lm″ (acc rsj) lj pjm (⊏⊑ pk) (⊏⊑ pk₁) pkj B₁ (g′ (to′ b₂))
                 (proj₂ Mx b₁ m1) (proj₂ My b₂ m2) (L.≤-trans m (H′ b₁ m1) (proj₁ My b₁ b₂ m1 m2 le)))))
    where
    kR : H k → H k
    kR b₂ = G (acc rsj) lj k (⊏⊑ pk₁) b₂ (G (acc rs″) lm″ j pjm (top b⊥ j) (g′ (to′ (fr₁ (to₁ b₂)))))
```

## 结论 (按档)

- **[定理]** 对一切 `I : CRwIf`, 一切可数层号 $m$, 目标 $t\lhd m$, 可达性与合法证明 (两边可不同): **`monoΦ`** (同底折叠对世界与输入联合单调, 值关系 `LeAt`), **`route`** (路线引理, 目标是中间层 $j$ 的真第一位置 `Pp t j`), **`MoΦ`** (保值合法); 辅助 `mΩ1`, `mΩΩ`, `rΩΩ`, `rK`, `kpG`, `moCh`, `chCmp`, 视图 `DV`, `dv`.
- 前提只有值合法 (`MoAt`) 与界在地板之上; 不要 `LgB` 之外的字面合法, 不读记号.
