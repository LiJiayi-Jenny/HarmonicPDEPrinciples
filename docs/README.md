# GitHub Pages 文档

站点入口是 <code>docs/index.md</code>。页面保留标准 Markdown，并由少量
JavaScript 将 <code>lean</code> 代码围栏升级为可编辑代码块。

部署配置位于 <code>.github/workflows/pages.yml</code>。仓库第一次推送到
GitHub 后，在 **Settings → Pages → Build and deployment → Source** 中选择
**GitHub Actions**；之后推送到 <code>main</code> 会自动更新站点。

本地 Lean 项目的完整验证命令：

~~~sh
lake build
~~~

GitHub Pages 是静态托管，在线代码检查由 Lean Web 的
<code>mathlib-stable</code> 项目完成。原始五文件项目仍以本地
<code>lake build</code> 的结果为准。
