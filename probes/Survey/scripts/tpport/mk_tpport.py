# 生成 TpPort 的克隆文件: 单种类主线上的 HtCrossV/MonoPort 文件搬到两种种类的折叠 HtTowerFFold 上.
# 用法 (从仓库根): python3 probes/Survey/scripts/tpport/mk_tpport.py .
# 每个文件: 源文件, 头注, 新的导入块, 逐字替换 (在公共变换之后).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tpgen import build

root = sys.argv[1]
AL = os.path.join(root, "probes/OCF/Align")

def rd(name):
    return open(os.path.join(AL, name + ".lagda.md")).read()

def wr(name, text):
    open(os.path.join(AL, name + ".lagda.md"), "w").write(text)

OPT = "{-# OPTIONS --safe --without-K --lossy-unification #-}"

def hdr(title, src, extra):
    return ("# " + title + "\n\n"
            "> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [" + src + "](" + src + ".lagda.md) "
            "逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), "
            "高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), "
            "数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. "
            + extra + "\n>\n"
            "> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.\n")

# ---------------------------------------------------------------- TpPortSim
SIM_IMP = OPT + """
module OCF.Align.TpPortSim where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB)
open import OCF.Align.HtTowerFTree renaming (_≤_ to _≤ʷ_)"""

def sim():
    src = rd("HtCrossVSim")
    extra = [
        ("zy₁ zy₂ ", "zy₁ zy₂ zz₁ zz₂ "),
        ("(zy₁ zy₂ zz₁ zz₂ : NZ ly)", "(zy₁ zy₂ : NZ ly) (zz₁ zz₂ : NZ₁ k → NZ₁ ly)"),
        ("Rl ly (Int a₁ x₁ q₀ lW zy₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀ lW zy₂ mk₂ u₂ w₂)",
         "Rl ly (Int a₁ x₁ q₀ lW zy₁ zz₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀ lW zy₂ zz₂ mk₂ u₂ w₂)"),
        ("(NZ-S R₁) (NZ-S R₂)", "(NZ-S R₁) (NZ-S R₂) (NZ₁-S R₁) (NZ₁-S R₂)"),
        ("⊲-tr", "≤tr"),
    ]
    h = hdr("两种种类的单调 (一): 不含回灌的互模拟", "HtCrossVSim",
            "`Free` 对两种种类的 Ω-极限都取 $\\bot$; `Int-R` 多两个参数 `zz₁`, `zz₂` (两种种类的 `Int` 的 `NZ₁` 搬运).")
    wr("TpPortSim", build(src, h, SIM_IMP, extra))

# ---------------------------------------------------------------- TpPortRun
RUN_IMP = OPT + """
module OCF.Align.TpPortRun where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB; ⊲ᴮ↑; cmpB)
open import OCF.Align.HtTowerFTree renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (ω⋅)
import OCF.Align.HtTowerFFold as Fold
open import OCF.Align.TpPortSim"""

def run():
    src = rd("HtCrossVRun")
    O1 = "(o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁)"
    O2 = "(o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂)"
    extra = [
        ("module Val (Λ : Ht) (lΛ : LgB Λ) where\n  open Fold ω⋅ Λ lΛ",
         "module Val (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) where\n  open Fold ω⋅ Λ lΛ oΛ"),
        ("module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂)",
         "module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) " + O1 + " (Λ₂ : Ht) (l₂ : LgB Λ₂) " + O2),
        ("module F₁ = Fold ω⋅ Λ₁ l₁", "module F₁ = Fold ω⋅ Λ₁ l₁ o₁"),
        ("module F₂ = Fold ω⋅ Λ₂ l₂", "module F₂ = Fold ω⋅ Λ₂ l₂ o₂"),
        ("module V₁ = Val Λ₁ l₁", "module V₁ = Val Λ₁ l₁ o₁"),
        ("module V₂ = Val Λ₂ l₂", "module V₂ = Val Λ₂ l₂ o₂"),
        ("(NZ-S r₁) (NZ-S r₂)", "(NZ-S r₁) (NZ-S r₂) (NZ₁-S r₁) (NZ₁-S r₂)"),
        ("⊲-tr", "≤tr"),
    ]
    h = hdr("两种种类的单调 (二): 两个实例里的折叠", "HtCrossVRun",
            "`Val`, `Two` 多实例的 `oΛ` (`o₁`, `o₂`); `Ai-R` 里内层 `Int-R` 多 `NZ₁-S` 两个参数. 关系里没有 `nκ`, `nμ` 的构造子, 所以折叠的 `nκ`, `nμ` 两句不出现.")
    wr("TpPortRun", build(src, h, RUN_IMP, extra))


# ---------------------------------------------------------------- 公共的参数头
def phead(name, extra_ty=""):
    return (OPT + "\nopen import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)\n"
            "open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)\n"
            "open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)\n" + extra_ty +
            "module OCF.Align." + name + " (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ)")

TREE = "open import OCF.Align.HtTowerFTree using ({}) renaming (_≤_ to _≤ʷ_)"
DEFN = "_⊑₀_; z0; o1; sq; lm; wl; wr; pr; tr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀"

# ---------------------------------------------------------------- TpPortDef
DEF_IMP = OPT + """
module OCF.Align.TpPortDef where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtTowerTy using (hz)
""" + TREE.format("D; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; sum; pt; sum-fst") + """

preL : ∀ {ly V} → (ℕ → D ly V) → ℕ → D ly V
preL d zero = n0
preL d (suc k) = preL d k ⨾ d k
"""

def defn():
    src = rd("StrRelDef")
    h = hdr("两种种类的单调 (三): 第 0 层的结构关系", "StrRelDef",
            "只取原文 §1 (`_⊑₀_`, `refl₀`, `nwd`, `preL₀`, `val₀`), 模块不带参数 (原文的参数只给 §2 以后用); `preL` 从原文的头部抄来.")
    wr("TpPortDef", build(src, h, DEF_IMP, keep_blocks=[2, 3]))

# ---------------------------------------------------------------- TpPortGen
GEN_IMP = phead("TpPortGen") + """ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
""" + TREE.format("n0; n1; _⨾_; nl; nw; sum; pt; sum-fst; ≤rf") + """
open import OCF.Align.HtTowerFClosed using (module At)"""

def gen():
    src = rd("MonoPort3Gen")
    extra = [("module P = At Λ lΛ", "module P = At Λ lΛ oΛ"), ("(tw : TW → A)", "(tw : TW → Wd₂)")]
    h = hdr("两种种类的单调 (四): 与关系无关的和结构核", "MonoPort3Gen",
            "原文导入而不使用的 `MonoPortBridge.smono` 去掉.")
    wr("TpPortGen", build(src, h, GEN_IMP, extra))

# ---------------------------------------------------------------- TpPortRelM
RELM_IMP = OPT + """
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerFTree using (Wd₂; LgW₂)
module OCF.Align.TpPortRelM {W : Wd₂} (lW : LgW₂ W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Data.Unit using (tt)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (hz; hs; hself; hsuc; _⊲[_]_)
""" + TREE.format("Ht; D; ss; StH; Vs; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf") + """
open import OCF.Align.TpPortDef using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL)
  renaming (tr to tr₀) public
"""

def relm():
    src = rd("MonoPort5Rel")
    extra = [("  OkRf {x = nκ z v} o = o", "  OkRf {x = nκ z v} o = o\n  OkRf {x = nμ z v} o = o")]
    h = hdr("两种种类的单调 (五): 一般层上的结构关系 `RelM`", "MonoPort5Rel",
            "只取原文的 `RelM` (原文其余是实例 $\\Lambda=3$ 的特例); `OkRf` 多 `nμ` 一句.")
    wr("TpPortRelM", build(src, h, RELM_IMP, extra, keep_blocks=[1]))

# ---------------------------------------------------------------- TpPortChn
CHN_IMP = OPT + """
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
import OCF.Align.TpPortGen as Gen
module OCF.Align.TpPortChn (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ)
  (O : Gen.OutLaws Λ lΛ oΛ lW t₀) (ly : Ht) (ac : AccY ly) (ll : ly ⊲[ W ] Λ)
  (Cx₀ In₀ : D ly W → D ly W → Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl)
""" + TREE.format("n0; _⨾_; nl; sum; pt; ≤rf")

def chn():
    src = rd("MonoPort5Chn")
    h = hdr("两种种类的单调 (六): 第 ≥1 层的上升链", "MonoPort5Chn", "")
    wr("TpPortChn", build(src, h, CHN_IMP))

# ---------------------------------------------------------------- TpPortZero
ZERO_IMP = OPT + """
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY)
import OCF.Align.TpPortGen as Gen
module OCF.Align.TpPortZero (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl)
""" + TREE.format("D; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; sum; pt; ≤rf; ≤tr") + """
open import OCF.Align.TpPortDef using (""" + DEFN + """; nwd; nwd′) renaming (preL to preLˢ)"""

def zero():
    src = rd("MonoPort6Zero")
    extra = [
        ("open Gen Λ lΛ oΛ lW t₀ using (module P; o₀; preL; module Core; OutLaws; PreLaw)",
         "open Gen Λ lΛ oΛ lW t₀ using (module P; o₀; preL; module Core; OutLaws; PreLaw)\n\n"
         "-- 两个 preL 字面相同 (原文从 MonoPort4Zero 导入)\n"
         "preL≡ : ∀ {V} (d : ℕ → D hz V) k → preLˢ d k ≡ preL d k\n"
         "preL≡ d zero = refl\n"
         "preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)"),
        ("ac ll A (λ V → V)", "ac ll Wd₂ (λ V → V)"),
    ]
    h = hdr("两种种类的单调 (七): 第 0 层的核与链", "MonoPort6Zero",
            "`preL≡` 由原文从 `MonoPort4Zero` 导入改为就地写出 (四行, 同原文).")
    wr("TpPortZero", build(src, h, ZERO_IMP, extra))

# ---------------------------------------------------------------- TpPortRel
REL_IMP = phead("TpPortRel") + """ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtTowerTy using (hl; hΩ; hself; hsuc; hlim; hLim)
""" + TREE.format("ss; sl; sL; StH; Vs; Vc; outC; inC; outS; inS; n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; sum; ≤rf") + """
open import OCF.Align.TpPortDef using (""" + DEFN + """; preL; val₀)
open import OCF.Align.TpPortRelM lW using (module RelM)
import OCF.Align.TpPortGen as Gen"""

def rel():
    src = rd("MonoPort7Rel")
    h = hdr("两种种类的单调 (八): 第 ≥1 层的结构关系", "MonoPort7Rel",
            "`Fin` 对两种种类的 Ω-极限都取 $\\bot$; 关系在 Ω-极限层上取 $\\top$, 同原文.")
    wr("TpPortRel", build(src, h, REL_IMP))

# ---------------------------------------------------------------- TpPortInt
INT_IMP = phead("TpPortInt") + """ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy using (hl; hΩ)
""" + TREE.format("ss; sl; sL; StH; Vs; NZ; NZ-S; NZ₁; NZ₁-S; acc; Int; Pre; mkOf; Kup; outS; inS; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; ≤tr") + """
open import OCF.Align.TpPortDef using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL)
  renaming (tr to tr₀; nwd to nwd₀; nwd′ to nwd₀′)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortRelM lW using (module RelM)"""

def int_():
    src = rd("MonoPort7Int")
    extra = [
        ("(zy : NZ ly) (mk : Mk k ly)", "(zy : NZ ly) (zy₁ : NZ₁ k → NZ₁ ly) (mk : Mk k ly)"),
        ("(zy : NZ ly) (mk : Mk L ly)", "(zy : NZ ly) (zy₁ : NZ₁ L → NZ₁ ly) (mk : Mk L ly)"),
        (" zy mk", " zy zy₁ mk"),
        ("(NZ-S r) mkR", "(NZ-S r) (NZ₁-S r) mkR"),
        ("Z.IntM₀ ly zy mu", "Z.IntM₀ ly zy zy₁ mu"),
        ("module Z (ly : Ht) (zy : NZ ly) where", "module Z (ly : Ht) (zy : NZ ly) (zy₁ : NZ₁ hz → NZ₁ ly) where"),
    ]
    h = hdr("两种种类的单调 (九): `Int` 单调", "MonoPort7Int",
            "两种种类的 `Int` 多一个参数 (`NZ₁` 的搬运), 所以 `ILpre`, `Z`, `IntMK`, `IntMS` 都多一个 `zy₁`; 节点一句内层 `Int` 多 `NZ₁-S r`.")
    wr("TpPortInt", build(src, h, INT_IMP, extra))

# ---------------------------------------------------------------- TpPortLay
LAY_IMP = phead("TpPortLay") + """ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.HtTowerTy using (⊲ᴮ↑)
""" + TREE.format("n0; _⨾_; nw; ≤rf") + """
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortRelM lW using (module RelM)
import OCF.Align.TpPortChn as Chn
import OCF.Align.TpPortGen as Gen"""

def lay():
    src = rd("MonoPort7Lay")
    h = hdr("两种种类的单调 (十): 层 $L$ 的核实例", "MonoPort7Lay", "")
    wr("TpPortLay", build(src, h, LAY_IMP))

# ---------------------------------------------------------------- TpPortSnd
SND_IMP = phead("TpPortSnd") + """ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtTowerTy using (hl; hΩ; ⊲ᴮ↑)
""" + TREE.format("ss; sl; sL; StH; Vs; acc; mkOf; inS; outS; NZ-S; NZ₁-S; n0; n1; _⨾_; nl; ni; nw; ≤rf") + """
open import OCF.Align.TpPortDef using (_⊑₀_; refl₀) renaming (preL to preLˢ)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortInt Λ lΛ oΛ lW t₀ using (IntMK; cx00; module CxS; cxLN; cxRN; finS; toN; fromN)
open import OCF.Align.TpPortLay Λ lΛ oΛ lW t₀ using (module L; HAKN)
open import OCF.Align.TpPortRelM lW using (module RelM)
import OCF.Align.TpPortZero as Z"""

def snd():
    src = rd("MonoPort7Snd")
    extra = [("  zL = NZ-S r\n", "  zL = NZ-S r\n  zL₁ = NZ₁-S r\n"), ("zL (mkOf r ≤rf)", "zL zL₁ (mkOf r ≤rf)")]
    h = hdr("两种种类的单调 (十一): 节点一步与对层的归纳", "MonoPort7Snd",
            "节点坐标动作的前提里, 内层 `Int` 多 `NZ₁-S r` (`zL₁`), 与两种种类的 `Ai` 字面一致.")
    wr("TpPortSnd", build(src, h, SND_IMP, extra))

# ---------------------------------------------------------------- TpPortNode
NODE_IMP = phead("TpPortNode") + """ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtTowerTy using (hl; hΩ; hself; ⊲ᴮ↑)
""" + TREE.format("ss; sl; sL; StH; Vs; acc; accᴸ; accK; accL; outS; n0; n1; _⨾_; nl; ni; nw; Ωd; sum; ≤rf; ≤tr") + """
open import OCF.Align.TpPortDef using (val₀)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortSnd Λ lΛ oΛ lW t₀ using (chainK; brnK; sndArg; OutsK)"""

def node():
    src = rd("MonoPort7Node")
    h = hdr("两种种类的单调 (十二): 常数分支的节点, 两边世界与嵌入不同; $\\Omega_k$ 的观测", "MonoPort7Node", "")
    wr("TpPortNode", build(src, h, NODE_IMP))

TARGETS = {"sim": sim, "run": run, "def": defn, "gen": gen, "relm": relm, "chn": chn, "zero": zero,
           "rel": rel, "int": int_, "lay": lay, "snd": snd, "node": node}


if __name__ == "__main__":
    which = sys.argv[2:] or list(TARGETS)
    for w in which:
        TARGETS[w]()
