/**
 * 箭头谜题破解器   适用：AutoX.js（Auto.js 系 Rhino 引擎）
 *
 * 棋盘 4×4，16 个槽位；每个槽位显示 ↑ → ↓ ← 四种朝向。
 * 点击槽位 n：以 n 为中心的 3×3 区域（含自身，越界丢弃，所以边上不足 9 格）各顺时针转 90°。
 *
 * 灰度：↑17  →39  ↓62  ←85，容差 ±5。
 * 目标：全部朝上（灰度 17）。
 *
 * 解完自动点击 (758,2124) 开始新一轮，连续多轮直到点悬浮按钮停止。
 * 本谜题不需要基准点，只用 16 个槽位的灰度。
 *
 * 求解：把“顺时针转 90°”记作 +1 (mod 4)，则每个点击是给邻域内各格 +1。
 *       于是问题变成解线性方程组 A·x ≡ b (mod 4)，用 GF(2) 两次求解（模2提升到模4），
 *       x_i 就是第 i 个格子要点几次（0~3 次）。因为加法可交换，点击顺序无所谓。
 *
 * 邻域按 4×4 二维数组计算：点 (r,c) 时遍历 r-1..r+1、c-1..c+1，
 * 行或列超出 0~3 的直接丢弃（不换行、不环绕）。
 *
 * 点右下角悬浮按钮开始 / 停止。
 */

var SLOT_X = [179, 420, 661, 902, 179, 420, 661, 902, 179, 420, 661, 902, 179, 420, 661, 902];
var SLOT_Y = [1138, 1138, 1138, 1138, 1369, 1369, 1369, 1369, 1599, 1599, 1599, 1599, 1850, 1850, 1850, 1850];

var GRAY = [17, 39, 62, 85];       // ↑ → ↓ ←
var ARROW = ["↑", "→", "↓", "←"];
var TOL = 5;                       // 灰度容差

var CLICK_DELAY = 250;             // 每次点击后等待(ms)
var NEXT_X = 758, NEXT_Y = 2124;   // 解完后点这里开始新一轮
var ROUND_DELAY = 1000;            // 新一轮加载等待(ms)
var DIALOG_OK_X = 600, DIALOG_OK_Y = 636;   // 结算面板“确定”的兜底坐标
var WIN_GRAY = 27, WIN_TOL = 3;    // 结束画面：16 格灰度全变 27（允许 ±3 误差）
var READ_RETRY = 4;                // 读棋盘重试次数
var MAX_FIX = 3;                   // 每轮最多补解次数

var working = false;
var roundNo = 0;
var emptyStreak = 0;
var busy = false;
var win = null;

/* --------------------------- 3×3 邻域（越界丢弃） --------------------------- */

// 点槽位 n（n 为 0~15，行优先：r = n / 4, c = n % 4）
// 受影响的是 r-1..r+1 行、c-1..c+1 列；行或列超出 0~3 的丢弃，不换行、不环绕
function affected(n) {
    var out = [];
    var r = Math.floor(n / 4), c = n % 4;
    for (var dr = -1; dr <= 1; dr++) {
        for (var dc = -1; dc <= 1; dc++) {
            var rr = r + dr, cc = c + dc;
            if (rr >= 0 && rr < 4 && cc >= 0 && cc < 4) out.push(rr * 4 + cc);
        }
    }
    return out;
}

function buildMatrix() {
    var A = [], i, j;
    for (i = 0; i < 16; i++) {
        A.push([]);
        for (j = 0; j < 16; j++) A[i].push(0);
    }
    for (var n = 0; n < 16; n++) {
        var cells = affected(n);
        for (var k = 0; k < cells.length; k++) A[cells[k]][n] = 1;  // 点 n 影响 cells[k]
    }
    return A;
}

/* ------------------------------ 棋盘读取 ------------------------------ */

function slotState(img, i) {
    var c = images.pixel(img, SLOT_X[i], SLOT_Y[i]);
    var g = Math.round(0.299 * colors.red(c) + 0.587 * colors.green(c) + 0.114 * colors.blue(c));
    var best = -1, bestD = 999;
    for (var k = 0; k < 4; k++) {
        var d = Math.abs(g - GRAY[k]);
        if (d < bestD) { bestD = d; best = k; }
    }
    return { v: bestD <= TOL ? best : -1, gray: g };
}

function readBoardOnce() {
    var img = captureScreen();
    if (!img) throw new Error("截图失败");
    try {
        var w = img.getWidth(), h = img.getHeight(), st = [], gs = [];
        for (var i = 0; i < 16; i++) {
            if (SLOT_X[i] >= w || SLOT_Y[i] >= h)
                throw new Error("槽位 " + (i + 1) + " 超出屏幕 " + w + "x" + h);
            var r = slotState(img, i);
            st.push(r.v);
            gs.push(r.gray);
        }
        var winAll = true;
        for (var k = 0; k < 16; k++) {
            if (Math.abs(gs[k] - WIN_GRAY) > WIN_TOL) { winAll = false; break; }
        }
        return { state: st, grays: gs, winScreen: winAll };
    } finally {
        try { img.recycle(); } catch (e) { }
    }
}

function isValid(st) {
    if (!st || st.length !== 16) return false;
    for (var i = 0; i < 16; i++) if (st[i] < 0 || st[i] > 3) return false;
    return true;
}

function readBoardStable() {
    var prev = null;
    for (var i = 0; i < READ_RETRY; i++) {
        var r = readBoardOnce();
        if (r.winScreen) return r;
        if (isValid(r.state)) {
            var s = r.state.join("");
            if (prev === s) return r;
            prev = s;
            sleep(120);
            continue;
        }
        prev = null;
        sleep(200);
    }
    return null;
}

function boardText(st) {
    var out = [];
    for (var r = 0; r < 4; r++) {
        var line = [];
        for (var c = 0; c < 4; c++) line.push(ARROW[st[r * 4 + c]]);
        out.push(line.join(" "));
    }
    return out.join("  /  ");
}

function isSolved(st) {
    for (var i = 0; i < 16; i++) if (st[i] !== 0) return false;
    return true;
}

/* ------------------------------ 线性求解 ------------------------------ */

// 解 A·x ≡ b (mod 2)，返回全部解（自由元枚举，最多 2^8 组）；无解返回 null
function solveMod2All(rowsMask, bBits) {
    var n = 16, rows = [], i, j;
    for (i = 0; i < n; i++) rows.push((rowsMask[i] & 0xFFFF) | ((bBits[i] & 1) << 16));

    var pivotCols = [], r = 0;
    for (var c = 0; c < n && r < n; c++) {
        var sel = -1;
        for (i = r; i < n; i++) if ((rows[i] >>> c) & 1) { sel = i; break; }
        if (sel < 0) continue;
        var t = rows[sel]; rows[sel] = rows[r]; rows[r] = t;
        for (i = 0; i < n; i++) if (i !== r && ((rows[i] >>> c) & 1)) rows[i] ^= rows[r];
        pivotCols.push(c);
        r++;
    }
    for (i = 0; i < n; i++) {
        if ((rows[i] & 0xFFFF) === 0 && ((rows[i] >>> 16) & 1)) return null;   // 无解
    }

    var isPivot = [], freeCols = [];
    for (j = 0; j < n; j++) isPivot.push(false);
    for (i = 0; i < pivotCols.length; i++) isPivot[pivotCols[i]] = true;
    for (j = 0; j < n; j++) if (!isPivot[j]) freeCols.push(j);
    if (freeCols.length > 8) return null;

    var sols = [], combos = 1 << freeCols.length;
    for (var m = 0; m < combos; m++) {
        var x = [];
        for (j = 0; j < n; j++) x.push(0);
        for (var f = 0; f < freeCols.length; f++) if ((m >>> f) & 1) x[freeCols[f]] = 1;
        for (var p = 0; p < pivotCols.length; p++) {
            var s = (rows[p] >>> 16) & 1;
            for (var f2 = 0; f2 < freeCols.length; f2++) {
                if (((rows[p] >>> freeCols[f2]) & 1) && x[freeCols[f2]]) s ^= 1;
            }
            x[pivotCols[p]] = s;
        }
        sols.push(x);
    }
    return sols;
}

function matVec(A, x) {
    var out = [], i, j;
    for (i = 0; i < 16; i++) {
        var s = 0;
        for (j = 0; j < 16; j++) if (A[i][j]) s += x[j];
        out.push(s % 4);
    }
    return out;
}

// 解 A·x ≡ b (mod 4)：把 x 拆成 x0(模2解) + 2u，枚举 x0 的所有模2解
function solveMod4(A, b) {
    var rowsMask = [], i, j, b2 = [];
    for (i = 0; i < 16; i++) {
        var m = 0;
        for (j = 0; j < 16; j++) if (A[i][j]) m |= (1 << j);
        rowsMask.push(m);
        b2.push(((b[i] % 4) + 4) % 4 % 2);
    }

    var base = solveMod2All(rowsMask, b2);
    if (!base) return null;

    for (var s = 0; s < base.length; s++) {
        var x0 = base[s];
        var ax = matVec(A, x0);
        var c = [], ok = true;
        for (i = 0; i < 16; i++) {
            var d = ((b[i] - ax[i]) % 4 + 4) % 4;
            if (d % 2 !== 0) { ok = false; break; }
            c.push(d / 2);
        }
        if (!ok) continue;

        var us = solveMod2All(rowsMask, c);
        if (!us) continue;
        for (var k = 0; k < us.length; k++) {
            var x = [];
            for (i = 0; i < 16; i++) x.push((x0[i] + 2 * us[k][i]) % 4);
            var chk = matVec(A, x);
            var good = true;
            for (i = 0; i < 16; i++) {
                if (chk[i] !== ((b[i] % 4) + 4) % 4) { good = false; break; }
            }
            if (good) return x;
        }
    }
    return null;
}

/* ------------------------------ 执行 ------------------------------ */

function applySolution(x) {
    var total = 0;
    for (var i = 0; i < 16; i++) {
        for (var k = 0; k < x[i]; k++) {
            if (!working) return total;
            click(SLOT_X[i], SLOT_Y[i]);
            sleep(CLICK_DELAY);
            total++;
        }
    }
    return total;
}

function checkCapture() {
    for (var i = 0; i < 3; i++) {
        var img = null;
        try { img = captureScreen(); } catch (e) { }
        if (img) { try { img.recycle(); } catch (e) { } return true; }
        try { if (typeof requestScreenCapture === "function") requestScreenCapture(); } catch (e) { }
        sleep(800);
    }
    return false;
}

/* ------------------------------ 结束画面 ------------------------------ */

// 结束画面：16 格全部变成向上的暗色箭头，灰度≈27（特效会有几个点误差），
// 而且往往还会弹一个带“确定”的结算面板挡住棋盘 —— 所以先按灰度 27 判定，再关面板。

function checkWinScreen() {
    var img = null;
    try { img = captureScreen(); } catch (e) { }
    if (!img) return false;
    try {
        for (var i = 0; i < 16; i++) {
            var c = images.pixel(img, SLOT_X[i], SLOT_Y[i]);
            var g = Math.round(0.299 * colors.red(c) + 0.587 * colors.green(c) + 0.114 * colors.blue(c));
            if (Math.abs(g - WIN_GRAY) > WIN_TOL) return false;
        }
        return true;
    } finally {
        try { img.recycle(); } catch (e2) { }
    }
}

function winDialogExists() {
    try {
        if (text("确定").exists()) return true;
        if (textContains("个人记录").exists()) return true;
    } catch (e) { }
    return false;
}

function dismissWinDialog() {
    if (!winDialogExists()) return false;
    try {
        var btn = text("确定").findOne(1500);
        if (btn) {
            btn.click();
            sleep(800);
            console.log("已点“确定”关闭结算面板");
            return true;
        }
    } catch (e) { }
    try {
        click(DIALOG_OK_X, DIALOG_OK_Y);
        sleep(800);
        console.log("已按坐标 (" + DIALOG_OK_X + "," + DIALOG_OK_Y + ") 点确定");
        return true;
    } catch (e2) { }
    return false;
}

function finishWin() {
    console.log("✔ 本局已完成（结束画面 16 格灰度≈" + WIN_GRAY + "）");
    dismissWinDialog();
    sleep(300);
    toast("已破解");
    return true;
}

/* ------------------------------ 主求解 ------------------------------ */

function solveBoard() {
    var rd = null;
    for (var tries = 1; tries <= 3; tries++) {
        rd = readBoardStable();
        if (rd) break;
        console.log("读盘没成功，等一下重试（第 " + tries + " 次）");
        sleep(800);
    }
    if (!rd) { console.log("✖ 读不到棋盘（灰度不符或画面被遮挡）"); return false; }

    if (rd.winScreen) {
        console.log("检测到结束画面（16 格灰度都是 " + WIN_GRAY + " 左右）");
        return finishWin();
    }

    console.log("初始：" + boardText(rd.state));

    if (isSolved(rd.state)) {
        sleep(500);
        var again = readBoardStable();
        if ((again && (again.winScreen || isSolved(again.state)))) {
            emptyStreak++;
            console.log("✔ 当前已全部朝上（连续 " + emptyStreak + " 次）");
            if (emptyStreak >= 5) {
                console.log("⚠ 连续 5 次都是已解状态，可能未进入对局，停止");
                return false;
            }
            return finishWin();
        }
        emptyStreak = 0;
        return solveBoard();
    }
    emptyStreak = 0;

    var A = buildMatrix();

    for (var attempt = 1; attempt <= MAX_FIX && working; attempt++) {
        var cur = readBoardStable();
        if (!cur) {
            if (checkWinScreen()) { console.log("出现结束画面 → 已完成"); return finishWin(); }
            console.log("✖ 中途读盘失败");
            break;
        }
        if (cur.winScreen) { console.log("出现结束画面 → 已完成"); return finishWin(); }
        if (isSolved(cur.state)) return finishWin();
        console.log((attempt === 1 ? "当前：" : "补解：") + boardText(cur.state));

        var b = [], j;
        for (j = 0; j < 16; j++) b.push((4 - cur.state[j]) % 4);

        var x = solveMod4(A, b);
        if (!x) { console.log("✖ 该局面无解"); return false; }

        var total = 0, plan = [];
        for (j = 0; j < 16; j++) total += x[j];
        for (j = 0; j < 16; j++) if (x[j] > 0) plan.push("槽位" + (j + 1) + "×" + x[j]);
        console.log("方案：共 " + total + " 次点击  " + plan.join("  "));

        var done = applySolution(x);
        console.log("已点击 " + done + " 次");
        if (!working) return false;

        // 点完等结束画面出来再判，别把结束画面当成“没解开”
        for (var w = 0; w < 3; w++) {
            sleep(300);
            if (checkWinScreen()) {
                console.log("出现结束画面 → 已完成");
                return finishWin();
            }
        }
    }

    if (checkWinScreen()) return finishWin();
    var fin = readBoardStable();
    if (fin && (fin.winScreen || isSolved(fin.state))) return finishWin();
    console.log("✘ 未完成：" + (fin ? boardText(fin.state) : "读盘失败"));
    toast("未完成");
    return false;
}

/* ------------------------------ 悬浮窗 ------------------------------ */

function applyUI(running) {
    try {
        win.label.setText(running ? "■" : "▶");
        win.root.attr("bg", running ? "#CCFF3B30" : "#CC2979FF");
    } catch (e) { }
}

function workLoop() {
    try {
        if (!checkCapture()) { console.log("✖ 截图权限不可用"); return; }
        while (working) {
            roundNo++;
            console.log("");
            console.log("===== 第 " + roundNo + " 轮 =====");

            var ok = solveBoard();
            if (!ok) {
                console.log("✘ 本轮没解开，先停下检查");
                break;
            }
            if (!working) break;

            // 有些版本点了“确定”就直接进下一局，先看一眼再决定要不要按开始键
            var next = readBoardStable();
            if (next && !next.winScreen && !isSolved(next.state)) {
                console.log("下一局已经出现，直接继续");
                continue;
            }
            if (!working) break;
            click(NEXT_X, NEXT_Y);
            console.log("已点击 (" + NEXT_X + "," + NEXT_Y + ")，等待新一轮");
            sleep(ROUND_DELAY);
        }
    } catch (e) {
        console.log("✖ 出错：" + (e && e.message ? e.message : e));
    } finally {
        working = false;
        busy = false;
        try { ui.run(function () { applyUI(false); }); } catch (e2) { }
        console.log("已停止，累计 " + roundNo + " 轮");
    }
}

function onTap() {
    if (working) {
        working = false;
        applyUI(false);
        console.log("■ 已停止");
        toast("已停止");
        return;
    }
    if (busy) { toast("还在收尾，稍等"); return; }
    busy = true;
    working = true;
    applyUI(true);
    console.log("▶ 开始");
    threads.start(function () { workLoop(); });
}

/* ------------------------------- 主流程 ------------------------------- */

function main() {
    console.show();
    console.setSize(0.92, 0.5);
    console.log("箭头谜题破解器（16 格）");
    console.log("目标：全部 ↑（灰度 17）；结束画面 16 格灰度≈" + WIN_GRAY);
    console.log("点右下角悬浮按钮开始 / 停止");

    var density = 1;
    try { density = context.getResources().getDisplayMetrics().density; } catch (e) { }
    var btnPx = Math.round(56 * density);
    var margin = Math.round(10 * density);

    win = floaty.window(
        '<frame id="root" w="56" h="56" bg="#CC2979FF">' +
        '<text id="label" w="56" h="56" gravity="center" text="▶" textSize="20sp" textColor="#FFFFFF"/>' +
        '</frame>'
    );
    try { win.setAdjustEnabled(false); } catch (e) { }
    try {
        win.setPosition(device.width - btnPx - margin,
            device.height - btnPx - Math.round(70 * density));
    } catch (e) { }

    win.root.on("click", onTap);

    try { if (!auto.service) console.log("⚠ 无障碍服务未开启，点击会失败"); } catch (e) { }

    events.observeKey();
    events.onKeyDown("volume_down", function () {
        console.log("音量下键，退出");
        working = false;
        try { win.close(); } catch (e) { }
        exit();
    });

    toast("点右下角按钮开始破解");
    while (true) sleep(1000);
}

main();
