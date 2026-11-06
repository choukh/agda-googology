# $X_2$: 实例, 地板, 闭项

> 不含记号. 入口 [X2](X2.lagda.md), 接口 [X2If](X2If.lagda.md), 折叠 [X2Fold](X2Fold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> 底是 [X1Up](X1Up.lagda.md) 的实例 `IU` ($X_1$, 世界是界 $B$, 序是字面第一位置). 本篇:
>
> 1. **层号** `ofU m` ($X_1$ 上叠可数层号 $m$) 与 $X_2=$ `lΩ lz (λ c → ls (ofU c))`. 折叠用的种类结构 `XS₂` 与 `Lv X₂` 逐子句同式, 只是分量 $c$ 写成 `X1UpFold.LS (hs c)` (`Lv (ls (ofU c))` 的同式拷贝): 两者对有限层号字面相同 (`comp-0`, `comp-1`, `refl`), 对变量层号不是同一函数 (ℕ-极限处的 `≡` 要函数外延; 否定一路 `NegX2Lv` §4 有不用外延的搬运, 本路没有用).
> 2. **种类的分类** `cls₂`: $X_2$ 自己的 $\Omega_1$ 种类是底的 $\Omega_1$ 种类 `κΩ` 的视图 (坐标同为第 0 层的值); 分支 $c$ 里底 $X_1$ 的种类 (`clD` 给 `bas`) 是它自己的视图; 分支 $c$ 里叠层的新种类 (`nw i`, $i+1\lhd c$) 与分支 $c$ 自己的新种类 (第 $X_1\oplus c$ 层) 是高种类, 层号在界之下的证据由 $c+1\lhd B$ 给出.
> 3. **换层** `cvK₂`: 分支 $c$ 的种类沿 $c+1\lhd B$ 嵌进第 $X_1\oplus B$ 层 (底种类 `emb`, 新种类 `along`, 同 `X1UpFold`); $X_2$ 自己的 $\Omega_1$ 种类不可换 (`CvK₂ = ⊥`).
> 4. **路径搬运** `liftOK`, `PH-cv`: 分支的路径结构是各分量的 `PSL (hs c)` 的并 (`PS₂`); 换层后在 `PSL B` 里带路径. 搬运只用序 (同 `X1UpFold.clP`, `upkE`, `upkA`).
> 5. **地板** `topL₂` ($\Omega_1$ 结点, 分支 $g\,(c+1)=g\,c\boxplus\iota_c\,\Omega_{\Omega_1+c+1}$, PathOut `topL` 的形状), 合法 (`Lg-topL₂`), 带路径 (`PH₂-top`, 对一切世界). **闭项** `TX2`, 证书 `LgB-TX2` (标准 `LgB`), FGH `fghX2`.
> 6. **边界 (定理)** `no-ΩΩ`: 两个地板之和 `topL₂ ⊞ topL₂` 不带路径: 高种类的分支里出现 $X_2$ 自己的 $\Omega_1$ 结点, 不可换层.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.X2Inst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv)
open import OCF.Align.TySupC using (Cd; _⊏ᶜ_)
open import OCF.Align.TySup using (ord⊥)
open import OCF.Align.PathOutX1 using (X₁; XS₁; κΩ; Ev₁; Adm₁; nxt₁)
open import OCF.Align.PathOut using (W₀; lW₀; sh→lgB₁)
open import OCF.Align.X1UpIf using (PS; module PS; PHg)
open import OCF.Align.X1Up using (IU; _≼₁_)
import OCF.Align.X1UpFold as UF
open UF IU using (LS; topU; ClD; bas; nw; clD; ClP; clP; emb; frE; along; frA; evE; upkE; evA; upkA;
                  PSL; PHU; psSup; psStep; PH-⊞; PH-mono; PH-up; PH-topU; Lg-topU)
open import OCF.Align.X2If renaming (up to upK)
import OCF.Align.X2Fold as XF
import OCF.Free.Level as FLv
```

## §1 层号与种类结构

```agda
ofU : Cd → LH
ofU hz = X₁
ofU (hs x) = ls (ofU x)
ofU (hl f) = ll (λ n → ofU (f n))
ofU (hΩ () _)

X₂ : LH
X₂ = lΩ lz (λ c → ls (ofU c))

G₂ : ⊤ ⊎ Cd → KS
G₂ = [ (λ _ → step S⊥) , (λ c → LS (hs c)) ]′

XS₂ : KS
XS₂ = sup (⊤ ⊎ Cd) G₂

-- X₂ 自己的 Ω₁ 种类
κΩ₂ : K XS₂
κΩ₂ = inj₁ tt , inj₂ tt
```

**与 `Lv X₂` 的关系 (定理, 有限层号).** `Lv X₂` 的第 $c$ 个分量是 `Lv (ls (ofU c))`; 对 $c=0,1$ 与 `G₂` 的分量字面相同.

```agda
comp-Ω : G₂ (inj₁ tt) ≡ step (Lv lz)
comp-Ω = refl

comp-0 : G₂ (inj₂ hz) ≡ Lv (ls (ofU hz))
comp-0 = refl

comp-1 : G₂ (inj₂ (hs hz)) ≡ Lv (ls (ofU (hs hz)))
comp-1 = refl
```

## §2 证据与分类

种类 `(inj₂ c , κ)` 的证据: 分支的坐标在界之下 ($c+1\lhd B$), 加上 $\kappa$ 在第 $X_1\oplus(c+1)$ 层的路径结构里的证据 (底种类是 $X_1$ 的证据, 新种类无证据). $X_2$ 自己的 $\Omega_1$ 种类无证据.

```agda
_⊏tr_ : ∀ {i c B} → i ⊏ᶜ c → c ⊏ᶜ B → i ⊏ᶜ B
p ⊏tr q = ⊲ᴮ-tr p (⊲ᴮ-tr (hsuc hself) q)

Ev₂ : Cd → K XS₂ → Set
Ev₂ B (inj₁ _ , _) = ⊤
Ev₂ B (inj₂ c , κ) = (c ⊏ᶜ B) × PS.Ev (PSL (hs c)) B κ

idW : Cd → Cd
idW B = B

clsC : ∀ {B} c κ′ → c ⊏ᶜ B → (d : ClD c κ′) → ClP c κ′ d → PS.Ev (PSL c) B κ′ →
       ClX IU XS₂ idW B (inj₂ c , inj₁ κ′)
clsC c κ′ q (bas κ₀ to) (evd , _) ev = lo κ₀ (evd ev) to
clsC c κ′ q (nw i pi to) _ ev = upK i (pi ⊏tr q) to

cls₂ : ∀ B κ → Ev₂ B κ → ClX IU XS₂ idW B κ
cls₂ B (inj₁ _ , inj₁ ()) _
cls₂ B (inj₁ _ , inj₂ _) _ = lo κΩ tt (λ y → y)
cls₂ B (inj₂ c , inj₂ _) (q , _) = upK c q (λ v → v)
cls₂ B (inj₂ c , inj₁ κ′) (q , ev) = clsC c κ′ q (clD c κ′) (clP c κ′) ev
```

## §3 换层

```agda
CvK₂ : Cd → K XS₂ → Set
CvK₂ B (inj₁ _ , _) = ⊥
CvK₂ B (inj₂ c , _) = c ⊏ᶜ B

lfK : ∀ B {c κ′} → c ⊏ᶜ B → ClD c κ′ → K (LS B)
lfK B q (bas κ₀ to) = emb B κ₀
lfK B q (nw i pi to) = along (pi ⊏tr q)

lfE : ∀ B {c κ′} (q : c ⊏ᶜ B) (d : ClD c κ′) → E (LS B) (lfK B q d) → E (LS c) κ′
lfE B q (bas κ₀ to) e = to (frE B κ₀ e)
lfE B q (nw i pi to) e = to (frA (pi ⊏tr q) e)

cvK₂ : ∀ B κ → CvK₂ B κ → K (LS B)
cvK₂ B (inj₁ _ , _) ()
cvK₂ B (inj₂ c , inj₂ _) q = along q
cvK₂ B (inj₂ c , inj₁ κ′) q = lfK B q (clD c κ′)

cvE₂ : ∀ B κ (k : CvK₂ B κ) → E (LS B) (cvK₂ B κ k) → E XS₂ κ
cvE₂ B (inj₁ _ , _) ()
cvE₂ B (inj₂ c , inj₂ _) q e = frA q e
cvE₂ B (inj₂ c , inj₁ κ′) q e = lfE B q (clD c κ′) e

I₂ : X2If
I₂ = record
  { U = IU ; XS₂ = XS₂ ; lvW = idW ; lgW = proj₁ ; Ev₂ = Ev₂ ; cls = cls₂
  ; CvK = CvK₂ ; cvK = cvK₂ ; cvE = cvE₂ }

open XF I₂ using (CB; cv; PH₂; Ψ₂; Sh-Ψ₂)
```

## §4 分支的路径结构与换层后的路径

`PS₂`: 各分量的路径结构的并. 分量 $c$ 是 `PSL (hs c)` (`X1UpFold`); $\Omega_1$ 分量随便给一个 (换层排除它).

```agda
module Bot₂ where
  Ev₀ : Cd → K S⊥ → Set
  Ev₀ W ()
  Adm₀ : (W : Cd) (κ : K S⊥) → E S⊥ κ → Set
  Adm₀ W ()
  nxt₀ : (W : Cd) (κ : K S⊥) → Ev₀ W κ → (e : E S⊥ κ) → Adm₀ W κ e → Cd
  nxt₀ W ()
  ev↑₀ : ∀ {W W′} → W ≼₁ W′ → ∀ {κ} → Ev₀ W κ → Ev₀ W′ κ
  ev↑₀ q {()}
  adm↓₀ : ∀ {W W′} (q : W ≼₁ W′) {κ} (ev : Ev₀ W κ) {e} (a′ : Adm₀ W′ κ e) →
          Σ (Adm₀ W κ e) (λ a → nxt₀ W κ ev e a ≼₁ nxt₀ W′ κ (ev↑₀ q {κ} ev) e a′)
  adm↓₀ q {()}
  ≼nx₀ : ∀ {W κ} (ev : Ev₀ W κ) e (a : Adm₀ W κ e) → W ≼₁ nxt₀ W κ ev e a
  ≼nx₀ {κ = ()}

psBot : PS _≼₁_ S⊥
psBot = record { Ev = Ev₀ ; Adm = Adm₀ ; nxt = nxt₀ ; ev↑ = ev↑₀ ; adm↓ = adm↓₀ ; ≼nx = ≼nx₀ }
  where open Bot₂

QS : (i : ⊤ ⊎ Cd) → PS _≼₁_ (G₂ i)
QS (inj₁ _) = psStep psBot
QS (inj₂ c) = PSL (hs c)

PS₂ : PS _≼₁_ XS₂
PS₂ = psSup QS

PHX : Cd → HB XS₂ → Set
PHX = PHg PS₂
```

**种类的搬运 (定理).** 分支 $c$ 的种类 $\kappa$ 换到第 $X_1\oplus B$ 层: 证据搬过去; 换后的可入读回换前的可入, 进入后的世界有序 (换前 $\preceq$ 换后). 底种类经 $X_1$ 的种类 $\kappa_0$ 中转 (`clP` 与 `upkE`), 新种类经 Kripke 世界 $V'$ 中转 (`clP` 与 `upkA`).

```agda
LiftOK : ∀ B c (κc : K (LS (hs c))) (q : c ⊏ᶜ B) → Set
LiftOK B c κc q =
  Σ (∀ {V} → PS.Ev (PSL (hs c)) V κc → PS.Ev (PSL B) V (cvK₂ B (inj₂ c , κc) q)) (λ evL →
    ∀ {V} (ev : PS.Ev (PSL (hs c)) V κc) e (a : PS.Adm (PSL B) V (cvK₂ B (inj₂ c , κc) q) e) →
      Σ (PS.Adm (PSL (hs c)) V κc (cvE₂ B (inj₂ c , κc) q e)) (λ a′ →
        PS.nxt (PSL (hs c)) V κc ev (cvE₂ B (inj₂ c , κc) q e) a′ ≼₁
        PS.nxt (PSL B) V (cvK₂ B (inj₂ c , κc) q) (evL ev) e a))

liftD : ∀ B c κ′ (q : c ⊏ᶜ B) (d : ClD c κ′) → ClP c κ′ d →
  Σ (∀ {V} → PS.Ev (PSL c) V κ′ → PS.Ev (PSL B) V (lfK B q d)) (λ evL →
    ∀ {V} (ev : PS.Ev (PSL c) V κ′) e (a : PS.Adm (PSL B) V (lfK B q d) e) →
      Σ (PS.Adm (PSL c) V κ′ (lfE B q d e)) (λ a′ →
        PS.nxt (PSL c) V κ′ ev (lfE B q d e) a′ ≼₁ PS.nxt (PSL B) V (lfK B q d) (evL ev) e a))
liftD B c κ′ q (bas κ₀ to) (evd , pk) =
  (λ ev → evE B κ₀ (evd ev)) ,
  λ ev e a →
    let u = upkE B κ₀ (evd ev) e a
        w = pk ev (frE B κ₀ e) (proj₁ u)
    in proj₁ w , ⊲ᴮ-tr (proj₂ w) (proj₂ u)
liftD B c κ′ q (nw i pi to) pk =
  (λ ev → evA (pi ⊏tr q)) ,
  λ ev e a →
    let u = upkA (pi ⊏tr q) (evA (pi ⊏tr q)) e a
        w = pk ev (frA (pi ⊏tr q) e) (proj₁ u) (proj₁ (proj₂ u)) (proj₁ (proj₂ (proj₂ u)))
    in proj₁ w , ⊲ᴮ-tr (proj₂ w) (proj₂ (proj₂ (proj₂ u)))

liftOK : ∀ B c κc q → LiftOK B c κc q
liftOK B c (inj₂ _) q =
  (λ _ → evA q) ,
  λ ev e a →
    let u = upkA q (evA q) e a
    in (proj₁ u , proj₁ (proj₂ u) , proj₁ (proj₂ (proj₂ u))) , proj₂ (proj₂ (proj₂ u))
liftOK B c (inj₁ κ′) q = liftD B c κ′ q (clD c κ′) (clP c κ′)
```

**换层保路径 (定理, 对一切世界 $V$ 与界 $B$).**

```agda
PH-cv : ∀ B V h (cb : CB B h) → PHX V h → PHU B V (cv B h cb)
PH-cv B V hz cb p = tt
PH-cv B V (hs h) cb p = PH-cv B V h cb p
PH-cv B V (hl f) cb p = λ n → PH-cv B V (f n) (cb n) (p n)
PH-cv B V (hΩ (inj₁ _ , κ) g) (() , _) p
PH-cv B V (hΩ (inj₂ c , κc) g) (q , cb) (ev , p) =
  proj₁ (liftOK B c κc q) ev , λ e a →
    PH-mono (PSL B) (proj₂ (proj₂ (liftOK B c κc q) ev e a)) _
      (PH-cv B _ (g (cvE₂ B (inj₂ c , κc) q e)) (cb _) (p _ (proj₁ (proj₂ (liftOK B c κc q) ev e a))))

PH-ι₂ : ∀ c (h : HB (LS (hs c))) {V} → PHU (hs c) V h → PHX V (ι (inj₂ c) h)
PH-ι₂ c hz p = tt
PH-ι₂ c (hs h) p = PH-ι₂ c h p
PH-ι₂ c (hl f) p = λ n → PH-ι₂ c (f n) (p n)
PH-ι₂ c (hΩ κ g) (ev , p) = ev , λ e a → PH-ι₂ c (g e) (p e a)
```

## §5 地板

`gt₂`: $g\,0=0$, $g\,(c+1)=g\,c\boxplus\iota_c\,\Omega_{\Omega_1+c+1}$ (第 $X_1\oplus(c+1)$ 层的地板 `topU (hs c)` 放进分量 $c$), $g(\lim f)=\lim(g\circ f)$. 同 `PathOut.gt`, 只是加数换成叠层的地板.

```agda
gt₂ : Cd → HB XS₂
gt₂ hz = hz
gt₂ (hs c) = gt₂ c ⊞ ι (inj₂ c) (topU (hs c))
gt₂ (hl f) = hl (λ n → gt₂ (f n))
gt₂ (hΩ () _)

topL₂ : HB XS₂
topL₂ = hΩ κΩ₂ gt₂

gt₂-⊲ : ∀ {a b} {w : Wd XS₂} → a ⊲[ tt ] b → gt₂ a ⊲[ w ] gt₂ b
gt₂-⊲ hself = hself
gt₂-⊲ (hsuc {b = b} p) = ⊲ᴮ-tr (gt₂-⊲ p) (⊞-fst (gt₂ b) (ι (inj₂ b) (topU (hs b))))
gt₂-⊲ (hlim n p) = hlim n (gt₂-⊲ p)
gt₂-⊲ (hLim {κ = ()} _ _)

Lg-gt₂ : ∀ c → LgB c → LgB (gt₂ c)
Lg-gt₂ hz l = tt
Lg-gt₂ (hs c) l =
  Lg-⊞ (gt₂ c) (ι (inj₂ c) (topU (hs c))) (Lg-gt₂ c l) (Lg-ι (inj₂ c) (topU (hs c)) (Lg-topU (hs c)))
Lg-gt₂ (hl f) (st , l) = (λ n → gt₂-⊲ (st n)) , (λ n → Lg-gt₂ (f n) (l n))
Lg-gt₂ (hΩ () _) l

Lg-topL₂ : LgB topL₂
Lg-topL₂ = (λ lw e e′ p → gt₂-⊲ p) , Lg-gt₂
```

**地板带路径 (定理, 对一切世界).** 分支 $y$ 里只有分量 $c$ ($c+1\lhd y+1$) 的高种类; 它们的分支对一切坐标可换层, 对带路径的坐标换层后带路径.

```agda
CB-ι : ∀ {B} c → c ⊏ᶜ B → (h : HB (LS (hs c))) → CB B (ι (inj₂ c) h)
CB-ι c q hz = tt
CB-ι c q (hs h) = CB-ι c q h
CB-ι c q (hl f) = λ n → CB-ι c q (f n)
CB-ι c q (hΩ κ g) = q , λ e → CB-ι c q (g e)

CB-⊞ : ∀ {B} a h → CB B a → CB B h → CB B (a ⊞ h)
CB-⊞ a hz ca ch = ca
CB-⊞ a (hs h) ca ch = CB-⊞ a h ca ch
CB-⊞ a (hl f) ca ch = λ n → CB-⊞ a (f n) ca (ch n)
CB-⊞ a (hΩ κ g) ca (k , ch) = k , λ e → CB-⊞ a (g e) ca (ch e)

CB-gt : ∀ {B} y → y ⊲[ tt ] B → CB B (gt₂ y)
CB-gt hz q = tt
CB-gt (hs c) q =
  CB-⊞ (gt₂ c) (ι (inj₂ c) (topU (hs c))) (CB-gt c (⊲ᴮ-tr (hsuc hself) q)) (CB-ι c q (topU (hs c)))
CB-gt (hl f) q = λ n → CB-gt (f n) (⊲ᴮ-tr (hlim n hself) q)
CB-gt (hΩ () _) q

PHX-gt : ∀ y V → PHX V (gt₂ y)
PHX-gt hz V = tt
PHX-gt (hs c) V =
  PH-⊞ PS₂ (gt₂ c) (ι (inj₂ c) (topU (hs c))) (PHX-gt c V) (PH-ι₂ c (topU (hs c)) (PH-topU (hs c) V))
PHX-gt (hl f) V = λ n → PHX-gt (f n) V
PHX-gt (hΩ () _) V

PH₂-gt : ∀ y V → y ⊲[ tt ] V → PH₂ V (gt₂ y)
PH₂-gt hz V q = tt
PH₂-gt (hs c) V q =
  (q , tt) ,
  (λ b′ → CB-⊞ (gt₂ c) (ι (inj₂ c) (up b′)) (CB-gt c (⊲ᴮ-tr (hsuc hself) q)) (CB-ι c q (up b′))) ,
  (λ b′ pb′ → PH-cv V V (gt₂ c ⊞ ι (inj₂ c) (up b′)) _
     (PH-⊞ PS₂ (gt₂ c) (ι (inj₂ c) (up b′)) (PHX-gt c V) (PH-ι₂ c (up b′) (PH-up c b′ pb′))))
PH₂-gt (hl f) V q = λ n → PH₂-gt (f n) V (⊲ᴮ-tr (hlim n hself) q)
PH₂-gt (hΩ () _) V q

PH₂-top : ∀ W → PH₂ W topL₂
PH₂-top W = tt , λ y a → PH₂-gt y (hs y) (hsuc hself)
```

## §6 闭项, 证书, FGH

`TX2`: $X_2$ 的地板经 `Ψ₂` 折到第 0 层, 初始世界 $B=1$, 当前界 $0$. 路径由定理 `PH₂-top` 给出.

```agda
TX2 : HB S⊥
TX2 = Ψ₂ W₀ lW₀ hz (z⊲ᴮ W₀) hz topL₂ (PH₂-top W₀)

LgB-TX2 : LgB TX2
LgB-TX2 = sh→lgB₁ TX2 (Sh-Ψ₂ W₀ lW₀ hz (z⊲ᴮ W₀) hz topL₂ (PH₂-top W₀))

fghX2 : ℕ → ℕ
fghX2 = FLv.FGH (ord⊥ TX2)
```

## §7 字面事实 (定理, refl)

$X_2$ 自己的 $\Omega_1$ 种类是低种类 (底 $\Omega_1$ 种类的视图); 分支 $1$ 的新种类 (第 $X_1\oplus1$ 层) 是高种类, 层号 $1$; 分支 $1$ 里底 $X_1$ 的 $\Omega_1$ 种类是低种类.

```agda
private
  one two : Cd
  one = hs hz
  two = hs one

  cls-root : cls₂ W₀ κΩ₂ tt ≡ lo κΩ tt (λ y → y)
  cls-root = refl

  cls-new : cls₂ two (inj₂ one , inj₂ tt) (hself , tt) ≡ upK one hself (λ v → v)
  cls-new = refl

  cls-base : cls₂ two (inj₂ one , inj₁ (inj₁ κΩ)) (hself , tt) ≡ lo κΩ tt (λ y → y)
  cls-base = refl
```

## §8 边界: 高种类的分支里不能有 $X_2$ 自己的 $\Omega_1$ 结点 (定理)

`topL₂ ⊞ topL₂` (读 $\Omega_{\Omega_1\cdot2}\cdot2$, 判断) 在世界 $1$ 里不带路径: 进入根结点的坐标 $2$ 后, 分支 $1$ 的新种类结点的第 $0$ 个分支, 其中分支 $0$ 的新种类结点的第 $0$ 个分支, 字面是 `topL₂`, 根是 $X_2$ 的 $\Omega_1$ 种类, 不可换层 (`CvK₂ = ⊥`).

```agda
no-ΩΩ : PH₂ W₀ (topL₂ ⊞ topL₂) → ⊥
no-ΩΩ (_ , p) = proj₁ (proj₂ (proj₁ (proj₂ (p (hs (hs hz)) (hsuc hself , tt))) hz) hz)
```
