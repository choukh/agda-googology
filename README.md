# Formal Googology in Agda

## 阅读入口

- [成品源码](src/README.md)：`Veblen/`、`WellFormed/`、`Bridged/`、`Lower.lagda.md` 与 `OCF/BTBO.lagda.md`。
- [Mahlo 研究](src/Mahlo/README.md)：研究从类型宇宙规则自动提取基本列，应用于 Mahlo 并认证 `F_{α_M}`；旧路线与探针已归档，尚非成品。
- [探针与历史探索](probes/README.md)：Lens 全部内容及 BTBO 之外的 OCF 探索，包含半成品、失败实验和待核查的结论。

默认 `make` 只发布成品文章；研究和探针不列入发布目标。

## Requirements

- [Agda 2.8.0](https://github.com/agda/agda/releases/tag/v2.8.0)
- [Agda Stdlib 2.4](https://github.com/agda/agda-stdlib/releases/tag/v2.4)
- [Cubical Agda 0.9](https://github.com/agda/cubical/releases/tag/v0.9)

将 `standard-library.agda-lib` 和 `cubical.agda-lib` 注册到
`~/.agda/libraries` 后，可运行 `tools/check-src.sh` 逐一检查 `src` 中的
全部 Agda 文件。项目库启用 `--guardedness`，因为 Cubical Agda 0.9
要求导入它的模块继承这一选项。

Agda 2.8 会拒绝旧版 Veblen 代码中的函数级非合流重写规则。迁移后的
`Finitary` 和 `Infinitary` 保留相应等式定理，并以显式等式替换完成证明；
无限元极限分支使用 Cubical 路径提供的函数外延性，不依赖 postulate。

## License

[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.en)
