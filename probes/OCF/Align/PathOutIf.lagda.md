# 路径记在折叠输出上: 接口

> 不含记号. 入口 [PathOut](PathOut.lagda.md). 构造一路 PathOut, 否定一路 NegPathOut 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **这一篇做什么.** [TySupIf](TySupIf.lagda.md) 的折叠只到可数层号. 推到 `lΩ` 层号 (共尾度 $\Omega_{k+1}$ 的层号, 如 $X_1=$ `lΩ lz (λ c → ls (ofC c))`) 时, 种类 `(inj₂ c , κ)` 的坐标 $c$ 是裸的, 精确的留/坍缩决定推出分离子 ([Fab4LOm](Fab4LOm.lagda.md) `exact→Sep`). 本接口不改层号与种类, 把 "路径" 放在折叠的状态与输出上:
>
> - **世界** `Wo`: 记一个字面下界 $B$ (实例里是 $\Omega_{k+1}$ 坐标的下界).
> - **目标在界之下** `Tg W t` (实例: $t\lhd B$); **种类的坐标在界之上** `Ev W κ` (实例: $B\lhd y$, $y$ 是种类的坐标). 两者经同一个 $B$ 连起来: 目标与种类的层号都落在种类自己的层号 $g\,y$ 之下, 那里有字面公共上界 ([Fab4LOm](Fab4LOm.lagda.md) `om-step` 的形状). 证据 `Ev` 不在种类里 (种类不动), 在折叠的输入上: 折叠的输入是 "带路径的高度" (`PathOutFold.PH`), 输出被再折时也要带它.
> - **带路径的回灌** `shift`: 进入一个分支时坐标先接在界后面 ($e\mapsto B\boxplus e'$), 所以进入的坐标字面在界之上 (`adm-shift`); 进入后世界换成新坐标 (`nxt`). 回灌不再是恒等.
> - **决定** `dec`: 目标与种类都带相对**同一世界**的证据, 世界合法. 没有对裸下标的比较律.
> - **决定正确** `correct` (回应 `NegTySupC.blind-TC`): 留 ⇒ 种类的层号严格在目标之下; 同层 ⇒ 层号就是目标; 在上 ⇒ 报的层就是种类的层号. 律的两个下标 (目标, 种类) 都带相对同一世界的字面证据.
>
> **接口定稿 2026-11-05 23:16 (首次编译通过).** 定稿后只增不改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.PathOutIf where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtTowerTy using (KS; K; E; HB)
open import OCF.Align.TySupIf using (TySupIf; module TySupIf)
```

## §1 带路径的决定

`DcP L _⊑_ LgC XS Tn t κ`: 输入种类结构 `XS` 的种类 $\kappa$ 对目标层 $t$ (目标层的值是 `HB (L t)`):

- `keep κ′ fr`: 留, 在 `L t` 里是种类 $\kappa'$, `fr` 把坐标读回.
- `same to`: 同层, 坍缩成链, `to` 把第 $t$ 层的值当坐标.
- `above i q li ti to`: 在上, 先坍缩到第 $i$ 层 ($t\sqsubseteq i$, $i$ 合法), `ti`: 新目标 $i$ 在一切分支世界的界之下.

```agda
data DcP {C : Set} (L : C → KS) (_⊑_ : C → C → Set) (LgC : C → Set) (XS : KS)
         (Tn : C → Set) (t : C) (κ : K XS) : Set where
  keep  : (κ′ : K (L t)) → (E (L t) κ′ → E XS κ) → DcP L _⊑_ LgC XS Tn t κ
  same  : (HB (L t) → E XS κ) → DcP L _⊑_ LgC XS Tn t κ
  above : (i : C) → t ⊑ i → LgC i → Tn i → (HB (L i) → E XS κ) → DcP L _⊑_ LgC XS Tn t κ

OkP : ∀ {C L _⊑_ LgC XS Tn t κ} (_⊏_ : C → C → Set) (j : C) → DcP {C} L _⊑_ LgC XS Tn t κ → Set
OkP {t = t} _⊏_ j (keep _ _) = j ⊏ t
OkP {t = t} _⊏_ j (same _) = j ≡ t
OkP _⊏_ j (above i _ _ _ _) = i ≡ j
```

## §2 记录

`R`: 可数层号的带类型折叠 (目标层与 "在上" 之后的折叠, 用 `TySupFold`). `XS`: 要折的 `lΩ` 层号的种类结构. 其余见文首.

```agda
record PathOutIf : Set₁ where
  field
    R : TySupIf
  open TySupIf R
  field
    XS     : KS
    Wo     : Set
    LgWo   : Wo → Set
    Tg     : Wo → C → Set
    Ev     : Wo → K XS → Set
    Adm    : (W : Wo) (κ : K XS) → E XS κ → Set
    nxt    : (W : Wo) (κ : K XS) → Ev W κ → (e : E XS κ) → Adm W κ e → Wo
    lg-nxt : ∀ {W κ} (ev : Ev W κ) e (a : Adm W κ e) → LgWo W → LgWo (nxt W κ ev e a)
    tg-nxt : ∀ {W κ t} (ev : Ev W κ) e (a : Adm W κ e) → Tg W t → Tg (nxt W κ ev e a) t
    shift  : (W : Wo) (κ : K XS) → E XS κ → E XS κ
    adm-shift : ∀ {W} κ e → LgWo W → Adm W κ (shift W κ e)
    lvX    : K XS → C
    -- 决定: 目标 t 与种类 κ 都带相对同一世界 W 的字面证据, W 合法
    dec    : ∀ W t → LgWo W → Tg W t → (κ : K XS) → (ev : Ev W κ) →
             DcP L _⊑_ LgC XS (λ i → ∀ e a → Tg (nxt W κ ev e a) i) t κ
    -- 决定正确 (律的两个下标带相对同一世界的证据)
    correct : ∀ W t (lW : LgWo W) (pt : Tg W t) κ (ev : Ev W κ) → OkP _⊏_ (lvX κ) (dec W t lW pt κ ev)
```
