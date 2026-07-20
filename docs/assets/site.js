(() => {
  "use strict";

  const LEAN_WEB = "https://live.lean-lang.org/";
  const LEAN_PROJECT = "mathlib-stable";

  const dialog = document.querySelector("#lean-dialog");
  const frame = document.querySelector("#lean-frame");
  const dialogTitle = document.querySelector("#lean-dialog-title");
  const externalLink = document.querySelector("#lean-dialog-external");
  const closeButton = document.querySelector(".lean-dialog-close");

  function makeLeanUrl(code) {
    const params = new URLSearchParams({ project: LEAN_PROJECT, code });
    return `${LEAN_WEB}#${params.toString()}`;
  }

  async function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      await navigator.clipboard.writeText(text);
      return;
    }

    const helper = document.createElement("textarea");
    helper.value = text;
    helper.setAttribute("readonly", "");
    helper.style.position = "fixed";
    helper.style.opacity = "0";
    document.body.appendChild(helper);
    helper.select();
    document.execCommand("copy");
    helper.remove();
  }

  function openLeanDialog(code, label) {
    const url = makeLeanUrl(code);
    if (!dialog || !frame || typeof dialog.showModal !== "function") {
      window.open(url, "_blank", "noopener,noreferrer");
      return;
    }

    dialogTitle.textContent = `${label} · Lean Web`;
    externalLink.href = url;
    frame.src = url;
    dialog.showModal();
  }

  const codeNodes = [
    ...document.querySelectorAll(".language-lean pre code, pre code.language-lean"),
  ];

  [...new Set(codeNodes)].forEach((codeNode, index) => {
    const source = codeNode.textContent.replace(/\n$/, "");
    const renderedBlock = codeNode.closest(".highlighter-rouge") || codeNode.parentElement;
    const label = `Lean 4 · 示例 ${index + 1}`;

    const widget = document.createElement("section");
    widget.className = "lean-widget";
    widget.setAttribute("aria-label", `${label} 可编辑代码块`);

    const toolbar = document.createElement("div");
    toolbar.className = "lean-toolbar";

    const title = document.createElement("span");
    title.className = "lean-label";
    title.textContent = label;

    const actions = document.createElement("div");
    actions.className = "lean-actions";

    const runButton = document.createElement("button");
    runButton.type = "button";
    runButton.className = "button button-primary";
    runButton.textContent = "在 Lean Web 运行";

    const openLink = document.createElement("a");
    openLink.className = "button";
    openLink.target = "_blank";
    openLink.rel = "noopener noreferrer";
    openLink.textContent = "新标签打开";

    const copyButton = document.createElement("button");
    copyButton.type = "button";
    copyButton.className = "button";
    copyButton.textContent = "复制";

    const resetButton = document.createElement("button");
    resetButton.type = "button";
    resetButton.className = "button";
    resetButton.textContent = "重置";

    actions.append(runButton, openLink, copyButton, resetButton);
    toolbar.append(title, actions);

    const editor = document.createElement("textarea");
    editor.className = "lean-editor";
    editor.value = source;
    editor.rows = Math.max(10, Math.min(26, source.split("\n").length + 1));
    editor.spellcheck = false;
    editor.setAttribute("aria-label", `${label} 编辑器`);

    const status = document.createElement("div");
    status.className = "lean-status";
    status.textContent = "可直接编辑；Ctrl/Command + Enter 在 Lean Web 中检查。";

    function refreshLink() {
      openLink.href = makeLeanUrl(editor.value);
      status.textContent = "代码已修改，尚未发送到 Lean Web。";
    }

    openLink.href = makeLeanUrl(source);
    editor.addEventListener("input", refreshLink);
    editor.addEventListener("keydown", (event) => {
      if (event.key === "Tab") {
        event.preventDefault();
        const start = editor.selectionStart;
        const end = editor.selectionEnd;
        editor.setRangeText("  ", start, end, "end");
        refreshLink();
      }

      if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) {
        event.preventDefault();
        openLeanDialog(editor.value, label);
      }
    });

    runButton.addEventListener("click", () => openLeanDialog(editor.value, label));
    copyButton.addEventListener("click", async () => {
      try {
        await copyText(editor.value);
        status.textContent = "已复制到剪贴板。";
      } catch (_error) {
        status.textContent = "浏览器阻止了复制，请手动选择代码。";
      }
    });
    resetButton.addEventListener("click", () => {
      editor.value = source;
      openLink.href = makeLeanUrl(source);
      status.textContent = "已恢复为文档中的原始示例。";
    });

    widget.append(toolbar, editor, status);
    renderedBlock.replaceWith(widget);
  });

  if (dialog && frame) {
    closeButton?.addEventListener("click", () => dialog.close());
    dialog.addEventListener("click", (event) => {
      if (event.target === dialog) dialog.close();
    });
    dialog.addEventListener("close", () => {
      frame.src = "about:blank";
    });
  }
})();
