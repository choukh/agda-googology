# Formal Googology in Agda

## 阅读入口

- [成品源码](src/README.md): `Veblen/`, `WellFormed/`, `Bridged/`, `Lower.lagda.md` 与 `OCF/BTBO.lagda.md`. 只收作者亲手写的成品文章.
- [探针](probes/README.md): 2026-11-01 起的新工作 (壁垒定理、交替路线、EBO 对齐), 及目录规则.
- [归档](archive/README.md): 此前的全部研究材料 (Mahlo 研究、旧 OCF 探针、Lens), 冻结只读.

总纲领与协作约定见 [AGENTS.md](AGENTS.md)。

默认 `make` 只发布成品文章；研究和探针不列入发布目标。

## Requirements

- [Agda 2.8.0](https://github.com/agda/agda/releases/tag/v2.8.0)
- [Agda Stdlib 2.4](https://github.com/agda/agda-stdlib/releases/tag/v2.4)
- [Cubical Agda 0.9](https://github.com/agda/cubical/releases/tag/v0.9)

将 `standard-library.agda-lib` 和 `cubical.agda-lib` 注册到
`~/.agda/libraries` 后，可运行 `tools/check-src.sh` 逐一检查 `src` 中的
全部 Agda 文件。项目库启用 `--guardedness`，因为 Cubical Agda 0.9
要求导入它的模块继承这一选项。

Veblen 三篇 (`Finitary`、`Infinitary`、`Transfinitary`) 把已证明的函数等式
注册为重写规则, 以便计算模式用 `refl` 证明。Agda 2.8 的局部合流检查会在
这些模块被导入时判定该规则非合流而报错 (单独检查却通过), 因此它们的
OPTIONS 不再开启 `--local-confluence-check`; 规则本身是已证明的命题等式,
不影响一致性。(2026-11-01 起; 此前一度改用显式等式替换, 已恢复。)

## License

[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.en)
