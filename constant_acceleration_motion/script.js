const canvas = document.getElementById("scene");
const ctx = canvas.getContext("2d");
const trackCanvas = document.getElementById("trackCanvas");
const tctx = trackCanvas.getContext("2d");
let W,
  H,
  running = false,
  lastTimestamp = 0,
  currentSimTime = 0,
  totalFlightTime = 0;
// Zoom state
let zoomLevel = 1.0,
  ZOOM_STEP = 1.15,
  ZOOM_MIN = 0.25,
  ZOOM_MAX = 5.0,
  lastTouchDist = null;
let charts = [],
  chartTypes = ["y", "vy", "ay"];
let probeY = 250,
  isDraggingProbe = false;
// remember the user's choice for Show Path Data even when graphs are hidden
let savedShowPathData = true;
// remember user's track ball preference when temporarily disabled for 'All Paths'
let savedTrackBallState = false;
let offsetX = 0,
  isPanning = false,
  startX = 0;
let verticalOffset = 0; // pixels added to default ground Y (positive -> ground moves down, more ground visible)
let panStartX = 0,
  panStartY = 0,
  panMode = null; // panMode: 'h' or 'v'
let panOrigOffsetX = 0,
  panOrigVerticalOffset = 0;
// global vector scale (pixels per m/s baseline)
let vectorScale = 2.5;

function updateVectorScale(el) {
  const v = parseFloat(el.value) || 1;
  vectorScale = v;
  const disp = document.getElementById("vectorScaleValue");
  if (disp) disp.textContent = vectorScale.toFixed(1);
  drawScene(currentSimTime);
}

function updateVectorShift(el) {
  const v = parseFloat(el.value) || 0;
  const disp = document.getElementById("vectorShiftValue");
  if (disp) disp.textContent = v.toFixed(0);
  // Vector shifting disabled — only update the displayed value and redraw.
  drawScene(currentSimTime);
}

function isHorizontalOnlyDetected() {
  try {
    const horizCheckbox = document.getElementById("horizontalMode");
    const horiz = !!(horizCheckbox && horizCheckbox.checked);
    const h0 = parseFloat((document.getElementById("height") || {}).value) || 0;
    const vMode =
      (document.getElementById("vModeToggle") || {}).value || "components";
    let vy0 = 0,
      angle = 0;
    if (vMode === "components")
      vy0 = parseFloat((document.getElementById("vy") || {}).value) || 0;
    else
      angle = parseFloat((document.getElementById("vAngle") || {}).value) || 0;
    const autoHoriz =
      (h0 <= 0 && Math.abs(vy0) < 1e-9) ||
      (vMode === "magnitude" && Math.abs(angle) < 1e-9);
    return horiz || autoHoriz;
  } catch (e) {
    return false;
  }
}

function isVerticalOnlyDetected() {
  try {
    const vMode =
      (document.getElementById("vModeToggle") || {}).value || "components";
    let vx0 = 0;
    if (vMode === "components")
      vx0 = parseFloat((document.getElementById("vx") || {}).value) || 0;
    else {
      const mag =
        parseFloat((document.getElementById("vMag") || {}).value) || 0;
      const ang =
        parseFloat((document.getElementById("vAngle") || {}).value) || 0;
      vx0 = mag * Math.cos((ang * Math.PI) / 180);
    }
    const gravity =
      parseFloat((document.getElementById("gravitySelect") || {}).value) || 0;
    // Consider vertical-only (free-fall) when horizontal velocity is essentially zero and gravity is present
    return Math.abs(vx0) < 1e-9 && Math.abs(gravity) > 1e-9;
  } catch (e) {
    return false;
  }
}

function isOneDimensionalMotionDetected() {
  try {
    // Treat motion as one-dimensional when either horizontal or vertical
    // component of the initial velocity is effectively zero. This allows
    // features like "Separate Overlapping Vectors" to appear for free-fall
    // (vx ≈ 0) even when initial height is non-zero.
    const horizDetected = isHorizontalOnlyDetected();
    if (horizDetected) return true;
    const vMode =
      (document.getElementById("vModeToggle") || {}).value || "components";
    let vx0 = 0,
      vy0 = 0;
    if (vMode === "components") {
      vx0 = parseFloat((document.getElementById("vx") || {}).value) || 0;
      vy0 = parseFloat((document.getElementById("vy") || {}).value) || 0;
    } else {
      const mag =
        parseFloat((document.getElementById("vMag") || {}).value) || 0;
      const ang =
        parseFloat((document.getElementById("vAngle") || {}).value) || 0;
      vx0 = mag * Math.cos((ang * Math.PI) / 180);
      vy0 = mag * Math.sin((ang * Math.PI) / 180);
    }
    const eps = 1e-9;
    return (
      Math.abs(vx0) < eps || Math.abs(vy0) < eps || isVerticalOnlyDetected()
    );
  } catch (e) {
    return false;
  }
}

function updateSeparateVectorsToggle(cb) {
  try {
    const cont = document.getElementById("vectorShiftContainer");
    const chk = document.getElementById("separateVectors");
    const outerLabel = document.getElementById("separateVectorsLabel");
    const allowed = isOneDimensionalMotionDetected();
    // show/hide the checkbox label depending on 1-D detection
    if (outerLabel) outerLabel.style.display = allowed ? "block" : "none";
    if (!allowed) {
      if (cont) cont.style.display = "none";
    } else {
      if (cont) cont.style.display = chk && chk.checked ? "flex" : "none";
    }
  } catch (e) {}
  drawScene(currentSimTime);
}

let savedPaths = [];
const PATH_COLORS = [
  "#D84315",
  "#2E7D32",
  "#1565C0",
  "#6A1B9A",
  "#F9A825",
  "#00838F",
  "#4527A0",
  "#AD1457",
  "#00796B",
  "#EF6C00",
];

// Temp arrays used each frame to avoid overlapping labels and to place callouts
let __currentLabelBoxes = [];
let __currentCalloutBoxes = [];
// Queue of labels to render as DOM KaTeX elements each frame
let vectorLabelQueue = [];
// Queue of vector draw commands for main canvas to decide overlap-based shifting
let pendingVectors = [];
// Cache used only when 1D separation is enabled; otherwise unused.
let vectorShiftCache = {};
let currentVectorOwner = "global";

function makeVectorKey(v) {
  const owner =
    v && v.owner
      ? String(v.owner)
      : typeof currentVectorOwner !== "undefined"
        ? String(currentVectorOwner)
        : "global";
  const lab = canonicalLabel(v && v.label ? v.label : "");
  // Use a stable key based on owner and canonical label (and whether it's an equation vector).
  // Avoid including coordinates so cached offsets persist across animation frames
  // and the user's `vectorShift` spacing remains applied consistently.
  return `${owner}|${lab}|${v.isEq ? 1 : 0}`;
}

function canonicalLabel(lbl) {
  if (!lbl) return "";
  let s = String(lbl).toLowerCase();
  s = s.replace(/\\/g, "").replace(/\{|\}/g, "").replace(/\s+/g, "");
  // map common variations
  if (/v0.*t|v₀.*t|v0t/.test(s)) return "v0t";
  if (/v0|v₀|v_0/.test(s)) return "v0";
  if (/1\/2|½/.test(s) && /a/.test(s) && /t\^?2|t²|t2/.test(s))
    return "half_at_t2";
  if (/a.*t|a·t|at/.test(s)) return "a_t";
  if (/\bdelta|\u0394|Δ|delta/.test(lbl)) return "delta";
  if (/\bs\b/.test(s) || s === "s") return "s";
  if (/\ba\b/.test(s) && !/a_t/.test(s)) return "a";
  if (/vx|v_x/.test(s)) return "vx";
  if (/vy|v_y/.test(s)) return "vy";
  return s.replace(/[^a-z0-9]/g, "");
}

function labelToLatex(lbl) {
  if (!lbl) return "";
  // normalize common labels to nicer LaTeX
  const map = {
    v: "\\vec{v}",
    v0: "\\vec{v}_0",
    v0t: "\\vec{v}_0\\,t",
    vx: "v_x",
    vy: "v_y",
    a: "\\vec{a}",
    s: "\\vec{s}",
    "v₀·t": "\\vec{v}_0 \\; t",
    "½ a·t²": "\\tfrac{1}{2} \\vec{a} \\; t^{2}",
    "v₀·t": "\\vec{v}_0 \\; t",
    "½ a·t²": "\\tfrac{1}{2} \\vec{a} \\; t^{2}",
    "v₀·t": "\\vec{v}_0 \\; t",
    "½ a·t²": "\\tfrac{1}{2} \\vec{a} \\; t^{2}",
    "\u0394x": "\\Delta x",
    "\u0394y": "\\Delta y",
    "\u0394x": "\\Delta x",
    "\u0394y": "\\Delta y",
  };
  if (map[lbl]) return map[lbl];
  // fallback: replace some unicode and symbols
  return lbl
    .replace(/Δ/g, "\\Delta ")
    .replace(/½/g, "\\tfrac{1}{2} ")
    .replace(/·/g, " ");
}

const graphOptions = [
  { val: "y", text: "y vs t" },
  { val: "vy", text: "vᵧ vs t" },
  { val: "ay", text: "aᵧ vs t" },
  { val: "x", text: "x vs t" },
  { val: "vx", text: "vₓ vs t" },
  { val: "ax", text: "aₓ vs t" },
  { val: "v_res", text: "|v| vs t" },
];

function toggleGraphs(cb) {
  const graphContainer = document.getElementById("graphContainer");
  const tableContainer = document.getElementById("pathTableContainer");
  if (!graphContainer) return;
  if (cb.checked) {
    graphContainer.style.display = "flex";
    // if table is visible, show only primary graph to the right
    if (tableContainer && tableContainer.style.display !== "none") {
      const graphWrappers = graphContainer.querySelectorAll(".graph-wrapper");
      graphWrappers.forEach((gw, i) => {
        if (i === 0) {
          gw.style.display = "flex";
          gw.style.flex = "1";
        } else gw.style.display = "none";
      });
    } else {
      // show all graphs side-by-side
      const graphWrappers = graphContainer.querySelectorAll(".graph-wrapper");
      graphWrappers.forEach((gw) => {
        gw.style.display = "flex";
        gw.style.flex = "1";
      });
    }
  } else {
    graphContainer.style.display = "none";
    // hide table option when graphs are off (enforced by updatePathDataOptionVisibility)
  }
  setTimeout(() => {
    window.dispatchEvent(new Event("resize"));
    if (Array.isArray(charts))
      charts.forEach((c) => c && c.resize && c.resize());
  }, 120);
  // adjust visibility of the Path Data option when graphs change
  try {
    updatePathDataOptionVisibility();
  } catch (e) {}
  try {
    updateSplitterVisibility();
  } catch (e) {}
}

// Show/hide the "Show Path Data" option and ensure the table is hidden when graphs are off
function updatePathDataOptionVisibility() {
  const label = document.getElementById("showPathDataLabel");
  const graphsCheckbox = document.getElementById("showGraphs");
  const pathCheckbox = document.getElementById("showPathData");
  const tableContainer = document.getElementById("pathTableContainer");
  if (!label || !graphsCheckbox) return;
  if (graphsCheckbox.checked) {
    label.style.display = "flex";
    // restore the previously saved show-path-data state
    if (pathCheckbox) {
      pathCheckbox.checked = savedShowPathData;
    }
    if (tableContainer)
      tableContainer.style.display = savedShowPathData ? "block" : "none";
  } else {
    // hide option and table when graphs are off but do NOT overwrite user's preference
    label.style.display = "none";
    if (tableContainer) tableContainer.style.display = "none";
  }
}
function populateDropdowns() {
  for (let i = 0; i < 3; i++) {
    const sel = document.getElementById(`sel${i}`);
    graphOptions.forEach((opt) => {
      let el = document.createElement("option");
      el.value = opt.val;
      el.textContent = opt.text;
      if (opt.val === chartTypes[i]) el.selected = true;
      sel.appendChild(el);
    });
  }
}

function toggleVMode() {
  const isComp = document.getElementById("vModeToggle").value === "components";
  document.getElementById("group-components").style.display = isComp
    ? "block"
    : "none";
  document.getElementById("group-magnitude").style.display = isComp
    ? "none"
    : "block";
  manualRefresh();
}

// Update UI state when horizontal-only mode is toggled: disable vertical controls and gravity
function updateHorizontalModeUI() {
  const horiz = !!(
    document.getElementById("horizontalMode") &&
    document.getElementById("horizontalMode").checked
  );
  const vy = document.getElementById("vy");
  const gravity = document.getElementById("gravitySelect");
  if (vy) {
    vy.disabled = horiz;
    try {
      const lab = vy.parentNode.querySelector("label");
      if (lab) lab.style.opacity = horiz ? "0.5" : "";
    } catch (e) {}
    if (horiz) vy.value = 0;
  }
  // disable angle input when horizontal-only mode is active
  const vAngle = document.getElementById("vAngle");
  if (vAngle) {
    vAngle.disabled = horiz;
    try {
      const labA = vAngle.parentNode.querySelector("label");
      if (labA) labA.style.opacity = horiz ? "0.5" : "";
    } catch (e) {}
    if (horiz) vAngle.value = 0;
  }
  // disable initial height when horizontal-only mode is active
  const heightEl = document.getElementById("height");
  if (heightEl) {
    heightEl.disabled = horiz;
    try {
      const lg =
        heightEl.parentNode && heightEl.parentNode.querySelector("legend");
      if (lg) lg.style.opacity = horiz ? "0.5" : "";
    } catch (e) {}
    if (horiz) heightEl.value = 0;
  }
  if (gravity) {
    gravity.disabled = horiz;
    try {
      const lg =
        gravity.parentNode && gravity.parentNode.querySelector("legend");
      if (lg) lg.style.opacity = horiz ? "0.5" : "";
    } catch (e) {}
  }
  // disable accel x and max-time when horizontal-only mode is NOT enabled
  const ax = document.getElementById("ax");
  const maxTimeEl = document.getElementById("maxTimeHorizontal");
  if (ax) {
    ax.disabled = !horiz;
    try {
      const labAx = ax.parentNode && ax.parentNode.querySelector("label");
      if (labAx) labAx.style.opacity = !horiz ? "0.5" : "";
    } catch (e) {}
  }
  if (maxTimeEl) {
    maxTimeEl.disabled = !horiz;
    try {
      const labT =
        maxTimeEl.parentNode && maxTimeEl.parentNode.querySelector("label");
      if (labT) labT.style.opacity = !horiz ? "0.5" : "";
    } catch (e) {}
  }
}

function togglePane(id, cb) {
  const pane = document.getElementById(id);
  pane.style.display = cb.checked ? "flex" : "none";
  drawScene(currentSimTime);
  // reposition summary overlay whenever the labels pane visibility changes
  try {
    positionResultsOverlay();
  } catch (e) {}
}

function getPhysics(t) {
  const h0 = Math.max(
    0,
    parseFloat(document.getElementById("height").value) || 0,
  );
  const g = parseFloat(document.getElementById("gravitySelect").value);
  let vx0 = 0,
    vy0 = 0;
  if (document.getElementById("vModeToggle").value === "components") {
    vx0 = parseFloat(document.getElementById("vx").value) || 0;
    vy0 = parseFloat(document.getElementById("vy").value) || 0;
  } else {
    const mag = parseFloat(document.getElementById("vMag").value) || 0;
    const ang = parseFloat(document.getElementById("vAngle").value) || 0;
    vx0 = mag * Math.cos((ang * Math.PI) / 180);
    vy0 = mag * Math.sin((ang * Math.PI) / 180);
  }
  // horizontal motion support: optional mode or auto-detect when on ground and vy0==0
  const horizMode = !!(
    document.getElementById("horizontalMode") &&
    document.getElementById("horizontalMode").checked
  );
  const axInput = parseFloat((document.getElementById("ax") || {}).value) || 0;
  const autoHoriz = h0 <= 0 && Math.abs(vy0) < 1e-9;
  if (horizMode || autoHoriz) {
    // horizontal motion constrained to ground: x(t)=vx0*t + 0.5*ax*t^2, y==0, vy==0
    // compute flight / stop time: if ax opposes vx0, the object may stop at tStop
    const maxTime =
      parseFloat((document.getElementById("maxTimeHorizontal") || {}).value) ||
      20.0;
    let tFlight = Math.max(0.01, maxTime); // user-configurable maximum duration when no stop
    if (Math.abs(axInput) > 1e-9) {
      const tStop = -vx0 / axInput; // time when vx reaches zero
      if (tStop > 0 && tStop < 100000) tFlight = Math.min(tStop, tFlight);
    }
    const actualT = Math.min(t, tFlight);
    const x = vx0 * actualT + 0.5 * axInput * actualT * actualT;
    const vx = vx0 + axInput * actualT;
    const vy = 0;
    const y = 0;
    const v_res = Math.abs(vx);
    const theta = vx >= 0 ? 0 : 180;
    return {
      t: actualT,
      x,
      y,
      vx,
      vy,
      g: 0,
      h0: 0,
      tFlight,
      tPeak: 0,
      yMax: 0,
      xMax: x,
      v_res,
      theta,
      ax: axInput,
      ay: 0,
    };
  }

  // default projectile motion
  const tFlight = (vy0 + Math.sqrt(vy0 * vy0 + 2 * g * h0)) / g;
  const actualT = Math.min(t, tFlight);
  return {
    t: actualT,
    x: vx0 * actualT,
    y: Math.max(0, h0 + vy0 * actualT - 0.5 * g * actualT * actualT),
    vx: vx0,
    vy: vy0 - g * actualT,
    g,
    h0,
    tFlight,
    tPeak: vy0 > 0 ? vy0 / g : 0,
    yMax: vy0 > 0 ? h0 + (vy0 * vy0) / (2 * g) : h0,
    xMax: vx0 * tFlight,
    v_res: Math.sqrt(vx0 * vx0 + (vy0 - g * actualT) ** 2),
    theta: (Math.atan2(vy0 - g * actualT, vx0) * 180) / Math.PI,
    ax: 0,
    ay: -g,
  };
}

// Return UI theme colors based on selected gravity (environment)
function getEnvTheme() {
  const gval =
    parseFloat((document.getElementById("gravitySelect") || {}).value) || 9.81;
  // default light brown ground (always use light brown per request)
  const ground = "rgba(222,198,153,0.28)";
  // default placeholders
  let theme = {
    sky: "#e3f2fd",
    skyLight: "#f0f7ff",
    ground: ground,
    grass: "rgba(140,200,120,0.20)",
    drawGrass: true,
    primary: "#1976D2",
    primaryDark: "#0d47a1",
    primaryRGBA: "rgba(25,118,210,0.9)",
    accel: "#d32f2f",
    accelRGBA: "rgba(211,47,47,0.9)",
    displacement: "#2e7d32",
    displacementRGBA: "rgba(46,125,50,0.9)",
    displacementRGBALight: "rgba(46,125,50,0.35)",
    displacementFill: "rgba(46,125,50,0.12)",
    btnActive: "#e6f4ff",
  };
  if (Math.abs(gval - 9.81) < 0.01) {
    // Earth
    theme.sky = "#e3f2fd";
    theme.skyLight = "#f0f7ff";
    theme.grass = "rgba(140,200,120,0.20)";
    theme.drawGrass = true;
    theme.primary = "#1976D2";
    theme.primaryRGBA = "rgba(25,118,210,0.9)";
    theme.primaryDark = "#0d47a1";
    theme.displacement = "#2e7d32";
    theme.displacementRGBA = "rgba(46,125,50,0.9)";
    theme.displacementRGBALight = "rgba(46,125,50,0.35)";
    theme.displacementFill = "rgba(46,125,50,0.12)";
    theme.accel = "#d32f2f";
    theme.accelRGBA = "rgba(211,47,47,0.9)";
    theme.btnActive = "#e6f4ff";
  } else if (Math.abs(gval - 1.62) < 0.01) {
    // Moon - pale gray sky, no grass
    theme.sky = "#f5f5f7";
    theme.skyLight = "#fbfbfc";
    theme.grass = "rgba(0,0,0,0)";
    theme.drawGrass = false;
    theme.primary = "#9e9e9e";
    theme.primaryRGBA = "rgba(158,158,158,0.9)";
    theme.primaryDark = "#757575";
    theme.displacement = "#8d6e63";
    theme.displacementRGBA = "rgba(141,110,99,0.9)";
    theme.displacementRGBALight = "rgba(141,110,99,0.35)";
    theme.displacementFill = "rgba(141,110,99,0.12)";
    theme.accel = "#b71c1c";
    theme.accelRGBA = "rgba(183,28,28,0.9)";
    theme.btnActive = "#f5f5f7";
  } else if (Math.abs(gval - 3.71) < 0.01) {
    // Mars - warm/orange tint
    theme.sky = "#fff2e6";
    theme.skyLight = "#fff7f0";
    theme.grass = "rgba(0,0,0,0)";
    theme.drawGrass = false;
    theme.primary = "#D84315";
    theme.primaryRGBA = "rgba(216,67,21,0.9)";
    theme.primaryDark = "#BF360C";
    theme.displacement = "#F57C00";
    theme.displacementRGBA = "rgba(245,124,0,0.9)";
    theme.displacementRGBALight = "rgba(245,124,0,0.35)";
    theme.displacementFill = "rgba(245,124,0,0.12)";
    theme.accel = "#B71C1C";
    theme.accelRGBA = "rgba(183,28,28,0.9)";
    theme.btnActive = "#fff3e0";
  } else if (Math.abs(gval - 24.79) < 0.01) {
    // Jupiter - pale beige/orange
    theme.sky = "#fff7e6";
    theme.skyLight = "#fff9f0";
    theme.grass = "rgba(0,0,0,0)";
    theme.drawGrass = false;
    theme.primary = "#FF8F00";
    theme.primaryRGBA = "rgba(255,143,0,0.9)";
    theme.primaryDark = "#EF6C00";
    theme.displacement = "#F9A825";
    theme.displacementRGBA = "rgba(249,168,37,0.9)";
    theme.displacementRGBALight = "rgba(249,168,37,0.35)";
    theme.displacementFill = "rgba(249,168,37,0.12)";
    theme.accel = "#D84315";
    theme.accelRGBA = "rgba(216,67,21,0.9)";
    theme.btnActive = "#fff8e1";
  } else if (Math.abs(gval - 274) < 1) {
    // Sun - very bright
    theme.sky = "#fffbe6";
    theme.skyLight = "#fffdf5";
    theme.grass = "rgba(0,0,0,0)";
    theme.drawGrass = false;
    theme.primary = "#FFB74D";
    theme.primaryRGBA = "rgba(255,183,77,0.9)";
    theme.primaryDark = "#FF9800";
    theme.displacement = "#FF8A65";
    theme.displacementRGBA = "rgba(255,138,101,0.9)";
    theme.displacementRGBALight = "rgba(255,138,101,0.35)";
    theme.displacementFill = "rgba(255,138,101,0.12)";
    theme.accel = "#E64A19";
    theme.accelRGBA = "rgba(230,74,25,0.9)";
    theme.btnActive = "#fff8e1";
  } else {
    // fallback
    theme = Object.assign(theme, {});
  }
  theme.ground = ground;
  return theme;
}

function saveCurrentPath() {
  const flight = getPhysics(0).tFlight;
  let data = [];
  for (let t = 0; t <= flight; t += 0.1) {
    data.push(getPhysics(t));
  }
  data.push(getPhysics(flight));
  const color = PATH_COLORS[savedPaths.length % PATH_COLORS.length];
  savedPaths.push({ visible: true, color: color, data: data, tFlight: flight });
  updatePathListUI();
  drawScene(currentSimTime);
}

function updatePathListUI() {
  const container = document.getElementById("pathList");
  container.innerHTML = "";
  savedPaths.forEach((path, idx) => {
    const row = document.createElement("div");
    row.className = "path-row";
    row.style.borderLeftColor = path.color;
    row.innerHTML = `
            <div class="path-label-group">
                <input type="checkbox" id="p${idx}" ${path.visible ? "checked" : ""} onchange="togglePath(${idx})">
                <label for="p${idx}">Path ${idx + 1}</label>
            </div>
            <button class="delete-btn" onclick="deletePath(${idx})" title="Delete Path">
                <i class="fas fa-trash-can"></i>
            </button>`;
    container.appendChild(row);
  });
  // refresh path data table when path list changes
  renderPathTables();
  // update the preview selector to reflect saved paths
  try {
    updatePreviewDropdown();
  } catch (e) {}
}

function togglePath(idx) {
  savedPaths[idx].visible = !savedPaths[idx].visible;
  drawScene(currentSimTime);
  if (
    document.getElementById("pathTableContainer") &&
    document.getElementById("pathTableContainer").style.display !== "none"
  )
    renderPathTables();
}

function deletePath(idx) {
  showConfirmDialog(
    "Delete Path",
    `Are you sure you want to delete Path ${idx + 1}?`,
    () => {
      savedPaths.splice(idx, 1);
      savedPaths.forEach(
        (p, i) => (p.color = PATH_COLORS[i % PATH_COLORS.length]),
      );
      updatePathListUI();
      drawScene(currentSimTime);
    },
  );
}

function clearAllPaths() {
  showConfirmDialog("Clear All Paths", "Clear all saved paths?", () => {
    savedPaths = [];
    updatePathListUI();
    drawScene(currentSimTime);
  });
}

function togglePathTables(cb) {
  const container = document.getElementById("pathTableContainer");
  const graphContainer = document.getElementById("graphContainer");
  const graphWrappers = graphContainer
    ? graphContainer.querySelectorAll(".graph-wrapper")
    : [];
  if (!container || !graphContainer) return;
  if (cb.checked) {
    // show table on left, single graph on right
    container.style.display = "block";
    container.style.flex = "0 0 55%";
    container.style.maxWidth = "55%";
    graphContainer.style.flexDirection = "row";
    // show only the primary graph (index 0) on the right
    graphWrappers.forEach((gw, i) => {
      if (i === 0) {
        gw.style.display = "flex";
        gw.style.flex = "1";
      } else {
        gw.style.display = "none";
      }
    });
  } else {
    // hide table, show three graphs side-by-side
    container.style.display = "none";
    container.style.flex = "";
    container.style.maxWidth = "";
    graphContainer.style.flexDirection = "row";
    graphWrappers.forEach((gw) => {
      gw.style.display = "flex";
      gw.style.flex = "1";
    });
  }
  // rebuild table contents and trigger chart resize after layout change
  renderPathTables();
  setTimeout(() => {
    window.dispatchEvent(new Event("resize"));
    if (Array.isArray(charts))
      charts.forEach((c) => c && c.resize && c.resize());
  }, 120);
  try {
    updateSplitterVisibility();
  } catch (e) {}
}

function updatePreviewDropdown() {
  const sel = document.getElementById("previewSelect");
  if (!sel) return;
  const prev = sel.value;
  sel.innerHTML = "";
  const curOpt = document.createElement("option");
  curOpt.value = "current";
  curOpt.text = "Current";
  sel.appendChild(curOpt);
  const allOpt = document.createElement("option");
  allOpt.value = "all";
  allOpt.text = "All Paths";
  sel.appendChild(allOpt);
  savedPaths.forEach((p, idx) => {
    const o = document.createElement("option");
    o.value = "p" + idx;
    o.text = "Path " + (idx + 1);
    sel.appendChild(o);
  });
  // restore previous selection if still available
  const found = Array.from(sel.options).some((o) => o.value === prev);
  sel.value = found ? prev : "current";
  // ensure time slider max reflects the selected preview
  const selVal = sel.value;
  if (selVal === "current") {
    totalFlightTime = getPhysics(0).tFlight;
  } else if (selVal === "all") {
    totalFlightTime = Math.max(
      getPhysics(0).tFlight,
      ...savedPaths.map((p) => p.tFlight || 0),
    );
  } else {
    const i = parseInt(selVal.slice(1));
    if (!isNaN(i) && savedPaths[i]) totalFlightTime = savedPaths[i].tFlight;
    else totalFlightTime = getPhysics(0).tFlight;
  }
  const slider = document.getElementById("timeSlider");
  if (slider) {
    slider.max = totalFlightTime;
    slider.step = "any";
    slider.value = Math.min(
      parseFloat(slider.value) || 0,
      parseFloat(slider.max) || 0,
    );
    try {
      renderScrubberTicks();
      updateScrubberUI(parseFloat(slider.value) || 0);
    } catch (e) {}
  }
  sel.onchange = () => {
    const v = sel.value;
    if (v === "current") totalFlightTime = getPhysics(0).tFlight;
    else if (v === "all")
      totalFlightTime = Math.max(
        getPhysics(0).tFlight,
        ...savedPaths.map((p) => p.tFlight || 0),
      );
    else {
      const i = parseInt(v.slice(1));
      if (!isNaN(i) && savedPaths[i]) totalFlightTime = savedPaths[i].tFlight;
    }
    const s = document.getElementById("timeSlider");
    if (s) s.max = totalFlightTime;
    currentSimTime = 0;
    if (s) s.value = 0;
    drawScene(0);
    try {
      renderScrubberTicks();
      updateScrubberUI(0);
    } catch (e) {}
    try {
      updateTrackBallAvailability();
    } catch (e) {}
  };
  // update track-ball availability when preview options change
  try {
    updateTrackBallAvailability();
  } catch (e) {}
  // hide launch summary immediately when 'All Paths' is selected
  try {
    const selv = sel.value;
    if (selv === "all") {
      const ov = document.getElementById("simulationResultsOverlay");
      if (ov) ov.style.display = "none";
    }
  } catch (e) {}
}

function updateTrackBallAvailability() {
  const sel = document.getElementById("previewSelect");
  const chk = document.getElementById("showTrackBall");
  const pane = document.getElementById("trackBallPane");
  if (!chk || !sel) return;
  const label = chk.parentNode;
  if (sel.value === "all") {
    // save current state and disable
    savedTrackBallState = !!chk.checked;
    chk.checked = false;
    chk.disabled = true;
    if (label) {
      label.style.opacity = "0.5";
      label.style.cursor = "not-allowed";
    }
    if (pane) pane.style.display = "none";
  } else {
    // restore
    chk.disabled = false;
    if (label) {
      label.style.opacity = "";
      label.style.cursor = "";
    }
    chk.checked = !!savedTrackBallState;
    // ensure pane visibility matches restored checkbox
    try {
      togglePane("trackBallPane", chk);
    } catch (e) {}
  }
}

function renderPathTables() {
  const holder = document.getElementById("pathTables");
  if (!holder) return;
  const t = currentSimTime || 0;
  const rows = [];
  savedPaths.forEach((p, idx) => {
    if (!p.visible) return;
    const s = samplePathStateAt(p, t);
    if (s) rows.push({ idx, color: p.color, s });
  });
  if (rows.length === 0) {
    holder.innerHTML =
      '<div style="color:#666">No paths selected. Check paths in the Path Manager to show their data.</div>';
    return;
  }

  // build a separate header table and a scrollable body table so header stays fixed
  let head = `<table class="path-table" style="font-size:0.95rem;"><thead><tr>`;
  head += `<th style="text-align:left;border-bottom:1px solid var(--border);">#</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">x (m)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">y (m)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">vx (m/s)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">vy (m/s)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">|v| (m/s)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">ax (m/s²)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">ay (m/s²)</th>`;
  head += `<th style="text-align:right;border-bottom:1px solid var(--border);">|a| (m/s²)</th>`;
  head += `</tr></thead></table>`;

  let body = `<div class="table-body"><table class="path-table"><tbody>`;
  rows.forEach((r) => {
    const s = r.s;
    const vres = Math.sqrt(
      (s.vx || 0) * (s.vx || 0) + (s.vy || 0) * (s.vy || 0),
    );
    const ares = Math.sqrt(
      (s.ax || 0) * (s.ax || 0) + (s.ay || 0) * (s.ay || 0),
    );
    body += `<tr>`;
    body += `<td><span class="path-swatch" style="background:${r.color}"></span><span class="path-number">${r.idx + 1}</span></td>`;
    body += `<td style="text-align:right;">${s.x.toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${s.y.toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${s.vx.toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${s.vy.toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${vres.toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${(s.ax || 0).toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${(s.ay || 0).toFixed(3)}</td>`;
    body += `<td style="text-align:right;">${ares.toFixed(3)}</td>`;
    body += `</tr>`;
  });
  body += `</tbody></table></div>`;

  holder.innerHTML = `<div class="table-wrapper">` + head + body + `</div>`;
}

// interpolate saved path state at time t
function samplePathStateAt(path, t) {
  if (!path || !path.data || path.data.length === 0) return null;
  const data = path.data;
  if (t <= data[0].t) return data[0];
  if (t >= data[data.length - 1].t) return data[data.length - 1];
  // find interval
  let lo = 0,
    hi = data.length - 1;
  while (lo <= hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (data[mid].t === t) return data[mid];
    if (data[mid].t < t) lo = mid + 1;
    else hi = mid - 1;
  }
  const i = Math.max(0, lo - 1);
  const a = data[i],
    b = data[i + 1];
  const f = (t - a.t) / (b.t - a.t);
  const interp = (k) => a[k] + (b[k] - a[k]) * f;
  // include metadata from saved path so drawScene has required values
  const last = data[data.length - 1] || {};
  const vx = interp("vx");
  const vy = interp("vy");
  const g = a.g !== undefined ? a.g : last.g !== undefined ? last.g : 9.81;
  return {
    t: t,
    x: interp("x"),
    y: interp("y"),
    vx: vx,
    vy: vy,
    ax: a.ax !== undefined ? interp("ax") : 0,
    ay: a.ay !== undefined ? interp("ay") : -g,
    h0: a.h0 !== undefined ? a.h0 : last.h0 !== undefined ? last.h0 : 0,
    g: g,
    tFlight: path.tFlight || last.tFlight || 0,
    yMax: last.yMax !== undefined ? last.yMax : Math.max(a.y || 0, b.y || 0),
    xMax: last.xMax !== undefined ? last.xMax : Math.max(a.x || 0, b.x || 0),
    v_res: Math.sqrt((vx || 0) * (vx || 0) + (vy || 0) * (vy || 0)),
    tPeak: last.tPeak !== undefined ? last.tPeak : 0,
    theta: (Math.atan2(vy, vx) * 180) / Math.PI,
  };
}

// Return the state to use for animation based on the preview selection.
function getPreviewState(t) {
  const sel = document.getElementById("previewSelect");
  if (sel && sel.value && sel.value !== "current") {
    const idx = parseInt(sel.value.slice(1));
    const p = savedPaths[idx];
    if (p) return samplePathStateAt(p, Math.min(t, p.tFlight));
  }
  return getPhysics(t);
}

// Return a summary-like state appropriate for showResults() based on preview
function getPreviewSummary() {
  const sel = document.getElementById("previewSelect");
  if (!sel || sel.value === "current") return getPhysics(totalFlightTime || 0);
  if (sel.value === "all") {
    // aggregate summary across paths
    const flight = Math.max(
      getPhysics(0).tFlight,
      ...savedPaths.map((p) => p.tFlight || 0),
    );
    const yMax = Math.max(
      ...savedPaths.map((p) =>
        p.data && p.data.length ? p.data[p.data.length - 1].yMax || 0 : 0,
      ),
      getPhysics(0).yMax || 0,
    );
    const xMax = Math.max(
      ...savedPaths.map((p) =>
        p.data && p.data.length ? p.data[p.data.length - 1].xMax || 0 : 0,
      ),
      getPhysics(0).xMax || 0,
    );
    const vres = Math.max(
      ...savedPaths.map((p) =>
        p.data && p.data.length ? p.data[p.data.length - 1].v_res || 0 : 0,
      ),
      getPhysics(0).v_res || 0,
    );
    return { tFlight: flight, yMax: yMax, xMax: xMax, tPeak: 0, v_res: vres };
  }
  const idx = parseInt(sel.value.slice(1));
  const p = savedPaths[idx];
  if (p && p.data && p.data.length) return p.data[p.data.length - 1];
  return getPhysics(totalFlightTime || 0);
}

function drawArrowImmediate(
  targetCtx,
  x,
  y,
  dx,
  dy,
  color,
  label = "",
  isEq = false,
) {
  const tox = x + dx,
    toy = y + dy;
  const angle = Math.atan2(dy, dx);
  const len = Math.hypot(dx, dy);
  if (len < 0.75) return; // effectively zero
  try {
    targetCtx.save();
    const focusOn =
      document.getElementById &&
      document.getElementById("focusEqVec") &&
      document.getElementById("focusEqVec").checked &&
      typeof activeKinematic !== "undefined" &&
      activeKinematic;
    if (focusOn && !isEq) targetCtx.globalAlpha = 0.25;
  } catch (e) {}
  const headlen = Math.min(10, Math.max(6, len * 0.25));
  targetCtx.strokeStyle = color;
  targetCtx.lineWidth = 2;
  if (len > headlen * 1.1) {
    targetCtx.beginPath();
    targetCtx.moveTo(x, y);
    targetCtx.lineTo(tox, toy);
    targetCtx.lineTo(
      tox - headlen * Math.cos(angle - Math.PI / 6),
      toy - headlen * Math.sin(angle - Math.PI / 6),
    );
    targetCtx.moveTo(tox, toy);
    targetCtx.lineTo(
      tox - headlen * Math.cos(angle + Math.PI / 6),
      toy - headlen * Math.sin(angle + Math.PI / 6),
    );
    targetCtx.stroke();
  } else {
    targetCtx.beginPath();
    const bx1 = tox - headlen * Math.cos(angle - Math.PI / 6);
    const by1 = toy - headlen * Math.sin(angle - Math.PI / 6);
    const bx2 = tox - headlen * Math.cos(angle + Math.PI / 6);
    const by2 = toy - headlen * Math.sin(angle + Math.PI / 6);
    targetCtx.moveTo(tox, toy);
    targetCtx.lineTo(bx1, by1);
    targetCtx.lineTo(bx2, by2);
    targetCtx.closePath();
    targetCtx.fillStyle = color;
    targetCtx.fill();
  }
  if (label) {
    try {
      if (targetCtx === ctx) {
        const midX = x + dx * 0.5;
        const midY = y + dy * 0.5;
        const perp = 10; // pixels offset away from the line
        const px = -Math.sin(angle) * perp;
        const py = Math.cos(angle) * perp;
        vectorLabelQueue.push({
          x: midX + px,
          y: midY + py,
          text: label,
          color: color,
          isEq: !!isEq,
        });
      }
    } catch (e) {}
  }
  try {
    targetCtx.restore();
  } catch (e) {}
}

function drawArrow(targetCtx, x, y, dx, dy, color, label = "", isEq = false) {
  // For main canvas, always queue arrows so they render after objects (so vectors appear on top).
  // For other drawing contexts (e.g., track preview canvas `tctx`) draw immediately.
  try {
    if (targetCtx !== ctx) {
      drawArrowImmediate(targetCtx, x, y, dx, dy, color, label, isEq);
      return;
    }
  } catch (e) {
    drawArrowImmediate(targetCtx, x, y, dx, dy, color, label, isEq);
    return;
  }
  // queue for per-frame processing (include owner so shifts are stable per-source)
  pendingVectors.push({
    x,
    y,
    dx,
    dy,
    color,
    label,
    isEq,
    owner:
      typeof currentVectorOwner !== "undefined" ? currentVectorOwner : "global",
  });
}

// (Removed) canvas callout helper — calculations are now shown in the DOM popup instead.

// Kinematic equation selector helpers
let activeKinematic = null;
function getKinematicEquation() {
  return activeKinematic;
}
function toggleKinematicEquation(id) {
  const prev = activeKinematic;
  if (prev === id) {
    activeKinematic = null;
  } else {
    activeKinematic = id;
  }
  // update button classes
  ["eq1", "eq2"].forEach((k) => {
    const b = document.getElementById("kinEq_btn_" + k);
    if (b) b.classList.toggle("active", activeKinematic === k);
  });
  applyKinematicSelection();
}
function applyKinematicSelection() {
  // Do not change user vector toggles — kinematic equations are now independent.
  try {
    drawScene(currentSimTime);
  } catch (e) {}
}

function updateTrackBall(state) {
  const tw = trackCanvas.width,
    th = trackCanvas.height;
  tctx.clearRect(0, 0, tw, th);
  const mode = document.getElementById("trackMode").value;
  const cx = tw / 2,
    cy = th / 2;
  if (mode === "focus") {
    const vs = 1.5 * (vectorScale / 2.5);
    const aScale = (vectorScale / 2.5) * 1.8; // keep original ratio but scale with vectorScale
    drawArrow(tctx, cx, cy, state.vx * vs, -state.vy * vs, "blue");
    drawArrow(tctx, cx, cy, state.vx * vs, 0, "rgba(0,0,255,0.3)");
    drawArrow(tctx, cx, cy, 0, -state.vy * vs, "rgba(0,0,255,0.3)");
    drawArrow(tctx, cx, cy, 0, state.g * aScale, "#d32f2f");
    tctx.fillStyle = "orange";
    tctx.beginPath();
    tctx.arc(cx, cy, 9, 0, Math.PI * 2);
    tctx.fill();
    tctx.stroke();
  } else {
    const miniScale = Math.min(
      (tw - 30) / Math.max(1, state.xMax),
      (th - 30) / Math.max(1, state.yMax),
    );
    const xOffset = 15 + (tw - 30 - state.xMax * miniScale) / 2;
    tctx.strokeStyle = "#bbb";
    tctx.setLineDash([3, 3]);
    tctx.beginPath();
    for (let i = 0; i <= state.tFlight; i += 0.1) {
      let p = getPhysics(i);
      tctx[i === 0 ? "moveTo" : "lineTo"](
        xOffset + p.x * miniScale,
        th - 15 - p.y * miniScale,
      );
    }
    tctx.stroke();
    tctx.setLineDash([]);
    tctx.fillStyle = "orange";
    tctx.beginPath();
    tctx.arc(
      xOffset + state.x * miniScale,
      th - 15 - state.y * miniScale,
      5,
      0,
      7,
    );
    tctx.fill();
    tctx.stroke();
  }
}

// Position the launch summary overlay relative to the data labels pane.
function positionResultsOverlay() {
  const overlay = document.getElementById("simulationResultsOverlay");
  const labels = document.getElementById("instantDetails");
  const container = document.getElementById("animationPane");
  if (!overlay || !container) return;
  // only position when visible
  if (
    overlay.style.display === "none" ||
    window.getComputedStyle(overlay).display === "none"
  )
    return;

  const containerRect = container.getBoundingClientRect();
  if (labels && window.getComputedStyle(labels).display !== "none") {
    const labRect = labels.getBoundingClientRect();
    const overlayW = overlay.offsetWidth || 170;
    // place overlay to the left of the labels pane with a small gap
    let leftPos = labRect.left - containerRect.left - overlayW - 12;
    if (leftPos < 8) leftPos = 8;
    overlay.style.left = leftPos + "px";
    overlay.style.right = "";
    overlay.style.transform = "";
    overlay.style.top = "15px";
  } else {
    // labels hidden - occupy the rightmost slot where labels would normally sit
    overlay.style.right = "15px";
    overlay.style.left = "";
    overlay.style.transform = "";
    overlay.style.top = "15px";
  }
}

function positionCalcPopup() {
  const popup = document.getElementById("calcPopup");
  const labels = document.getElementById("instantDetails");
  const container = document.getElementById("animationPane");
  if (!popup || !container) return;
  if (labels && window.getComputedStyle(labels).display !== "none") {
    const labRect = labels.getBoundingClientRect();
    const containerRect = container.getBoundingClientRect();
    // prefer placing the popup just under the labels pane, but clamp to animationPane bounds
    const desiredLeft = labRect.left - containerRect.left;
    const desiredTop = labRect.bottom - containerRect.top + 6;
    // limit popup width so it cannot escape the animation pane
    const maxW = Math.min(420, Math.max(160, containerRect.width - 40));
    popup.style.maxWidth = maxW + "px";
    popup.style.left = desiredLeft + "px";
    popup.style.top = desiredTop + "px";
    popup.style.display = "block"; // visible
    // adjust if the popup overflows right/bottom edges
    const pw = popup.offsetWidth || Math.min(200, maxW);
    const ph = popup.offsetHeight || 20;
    let left = desiredLeft;
    if (left + pw > containerRect.width - 12)
      left = Math.max(12, containerRect.width - pw - 12);
    if (left < 12) left = 12;
    let top = desiredTop;
    if (top + ph > containerRect.height - 12)
      top = Math.max(12, containerRect.height - ph - 12);
    popup.style.left = left + "px";
    popup.style.top = top + "px";
  } else {
    // position to rightmost slot under where labels would sit
    const containerRect = container.getBoundingClientRect();
    const maxW = Math.min(420, Math.max(160, containerRect.width - 40));
    popup.style.maxWidth = maxW + "px";
    // default right aligned with margin
    const pw = popup.offsetWidth || Math.min(200, maxW);
    let left = containerRect.width - pw - 15;
    if (left < 12) left = 12;
    let top = 15;
    if (top + (popup.offsetHeight || 20) > containerRect.height - 12)
      top = Math.max(
        12,
        containerRect.height - (popup.offsetHeight || 20) - 12,
      );
    popup.style.left = left + "px";
    popup.style.top = top + "px";
    popup.style.display = "block";
  }
}

// Position the equation graph pane next to the track ball (if visible) or in its default slot
function positionEquationGraph() {
  const pane = document.getElementById("equationGraphPane");
  const track = document.getElementById("trackBallPane");
  const container = document.getElementById("animationPane");
  if (!pane || !container) return;
  if (
    pane.style.display === "none" ||
    window.getComputedStyle(pane).display === "none"
  )
    return;
  const containerRect = container.getBoundingClientRect();
  if (track && window.getComputedStyle(track).display !== "none") {
    try {
      const tRect = track.getBoundingClientRect();
      // place to the right of the track pane
      let leftPos = tRect.right - containerRect.left + 8;
      if (leftPos + pane.offsetWidth > containerRect.width - 8)
        leftPos = containerRect.width - pane.offsetWidth - 8;
      pane.style.left = leftPos + "px";
      pane.style.top = tRect.top - containerRect.top + "px";
      pane.style.right = "";
      pane.style.transform = "";
    } catch (e) {
      pane.style.left = "15px";
      pane.style.top = "15px";
    }
  } else {
    // place in the default top-left slot where track ball normally is
    const left = 15;
    const top = 15;
    pane.style.left = left + "px";
    pane.style.top = top + "px";
    pane.style.right = "";
    pane.style.transform = "";
  }
}

function showEquationGraph() {
  const p = document.getElementById("equationGraphPane");
  if (p) p.style.display = "flex";
  positionEquationGraph();
}
function hideEquationGraph() {
  const p = document.getElementById("equationGraphPane");
  if (p) p.style.display = "none";
}

// Render the equation visualization (v_y vs t) into the small canvas.
function renderEquationGraph(t) {
  const theme = getEnvTheme();
  const pane = document.getElementById("equationGraphPane");
  if (!pane || pane.style.display === "none") return;
  const c = document.getElementById("eqGraphCanvas");
  if (!c) return;
  const ctxg = c.getContext("2d");
  const dpr = window.devicePixelRatio || 1;
  const Wc = c.width;
  const Hc = c.height;
  // clear
  ctxg.clearRect(0, 0, Wc, Hc);
  // get preview state (single preview only)
  const sel =
    (document.getElementById("previewSelect") || {}).value || "current";
  const horizMode = !!(
    document.getElementById("horizontalMode") &&
    document.getElementById("horizontalMode").checked
  );
  if (sel === "all") return; // don't show for 'all'
  const state = getPreviewState(t);
  const p0 = getPhysics(0);
  const tsec = state.t;
  // If horizontal-only, render v_x vs t using ax/vx; otherwise render v_y vs t
  let axisLabel = "v_y (m/s)";
  let v0 = p0.vy || 0;
  let a_comp = -(p0.g || getPhysics(0).g || 9.81);
  let vt = state.vy;
  if (horizMode) {
    axisLabel = "v_x (m/s)";
    v0 = p0.vx || 0;
    a_comp = p0.ax !== undefined ? p0.ax : getPhysics(0).ax || 0;
    vt = state.vx;
  }
  // compute plot range (0..tsec on x)
  const maxT = Math.max(
    1,
    Math.min(p0.tFlight || 5, Math.max(tsec, p0.tFlight || 1)),
  );
  // y range include vy0 and vt with margin
  const yMin = Math.min(vy0, vt, 0) - Math.abs(Math.max(vy0, vt)) * 0.25;
  const yMax = Math.max(vy0, vt, 0) + Math.abs(Math.max(vy0, vt)) * 0.25;
  const padL = 30,
    padR = 8,
    padT = 8,
    padB = 18;
  const plotW = Wc - padL - padR,
    plotH = Hc - padT - padB;
  function sx(x) {
    return Math.round(padL + (x / maxT) * plotW);
  }
  function sy(y) {
    return Math.round(padT + plotH - ((y - yMin) / (yMax - yMin || 1)) * plotH);
  }
  // axes
  ctxg.strokeStyle = "#ddd";
  ctxg.lineWidth = 1;
  ctxg.beginPath();
  ctxg.moveTo(padL, padT);
  ctxg.lineTo(padL, padT + plotH);
  ctxg.lineTo(padL + plotW, padT + plotH);
  ctxg.stroke();
  // plot v(t) as linear: v(t) = v0 + a_comp * t
  ctxg.strokeStyle = theme.primary;
  ctxg.lineWidth = 2;
  ctxg.beginPath();
  for (let tt = 0; tt <= tsec; tt += Math.max(0.01, tsec / 80)) {
    const vv = v0 + a_comp * tt;
    const x = sx(tt);
    const y = sy(vv);
    if (tt === 0) ctxg.moveTo(x, y);
    else ctxg.lineTo(x, y);
  }
  ctxg.stroke();
  // mark v0 at t=0
  const x0 = sx(0),
    y0 = sy(v0);
  ctxg.fillStyle = theme.primaryDark;
  ctxg.beginPath();
  ctxg.arc(x0, y0, 3, 0, 7);
  ctxg.fill();
  ctxg.fillStyle = theme.primaryDark;
  ctxg.font = "12px sans-serif";
  ctxg.fillText(horizMode ? "v_{x0}" : "v_{y0}", x0 + 6, y0 - 6);
  // mark vt at t
  const xt = sx(tsec),
    yt = sy(vt);
  ctxg.fillStyle = theme.primary;
  ctxg.beginPath();
  ctxg.arc(xt, yt, 3, 0, 7);
  ctxg.fill();
  ctxg.fillStyle = theme.primary;
  ctxg.fillText(horizMode ? "v_x(t)" : "v_y(t)", xt + 6, yt - 6);
  // show decomposition labels for eq1: v_y = v_{y0} + a_y t
  if (getKinematicEquation() === "eq1") {
    // draw segment representing a*t at time t from v0 to vt
    ctxg.strokeStyle = theme.accel;
    ctxg.lineWidth = 2;
    ctxg.beginPath();
    ctxg.moveTo(xt, y0);
    ctxg.lineTo(xt, yt);
    ctxg.stroke();
    // annotate
    ctxg.fillStyle = theme.accel;
    ctxg.fillText(
      horizMode ? "a_x\u00B7t" : "a_y\u00B7t",
      xt + 6,
      (y0 + yt) / 2,
    );
    ctxg.fillStyle = "#000";
    ctxg.fillText(
      horizMode ? "v_x = v_{x0} + a_x t" : "v_y = v_{y0} + a_y t",
      padL,
      padT - 2,
    );
  }
  // For eq2, shade area under curve from 0..t and decompose into rectangle (v0*t) and triangle (1/2 a t^2)
  if (getKinematicEquation() === "eq2") {
    // Build path for area under v(t)
    ctxg.save();
    // rectangle area for v0 * t
    const rx = sx(0),
      rw = sx(tsec) - sx(0);
    const ry = sy(v0);
    const rh = sy(Math.max(yMin, 0)) - ry;
    ctxg.fillStyle = "rgba(46,125,50,0.25)";
    ctxg.fillRect(rx, ry, rw, Math.max(1, sy(0) - ry));
    // triangular area for 1/2 a t^2 -> draw triangle between vy0 and vt
    ctxg.beginPath();
    ctxg.moveTo(sx(0), sy(v0));
    ctxg.lineTo(sx(tsec), sy(v0));
    ctxg.lineTo(sx(tsec), sy(vt));
    ctxg.closePath();
    ctxg.fillStyle = "rgba(46,125,50,0.12)";
    ctxg.fill();
    // outline shaded area
    ctxg.strokeStyle = theme.displacement;
    ctxg.lineWidth = 1;
    ctxg.beginPath();
    ctxg.moveTo(sx(0), sy(0));
    ctxg.lineTo(sx(tsec), sy(0));
    ctxg.stroke();
    // annotate labels
    ctxg.fillStyle = theme.displacement;
    ctxg.font = "12px sans-serif";
    ctxg.fillText(horizMode ? "v_{x0}·t" : "v_{y0}·t", rx + rw * 0.4, ry - 6);
    ctxg.fillText(
      horizMode ? "\u00BD a_x t^2" : "\u00BD a_y t^2",
      sx(tsec) - 40,
      sy(vt) + 14,
    );
    ctxg.fillStyle = "#000";
    ctxg.fillText(
      horizMode
        ? "s_x = v_{x0} t + 1/2 a_x t^2 (area)"
        : "s_y = v_{y0} t + 1/2 a_y t^2 (area)",
      padL,
      padT - 2,
    );
    ctxg.restore();
  }
  // axis labels
  ctxg.fillStyle = "#666";
  ctxg.font = "11px sans-serif";
  ctxg.fillText("t (s)", padL + plotW - 20, padT + plotH + 14);
  ctxg.fillText(axisLabel, 6, padT + 10);
  // update legend
  const legend = document.getElementById("eqGraphLegend");
  if (legend) {
    if (getKinematicEquation() === "eq1")
      legend.innerHTML = horizMode
        ? `<span style="color:${theme.primaryDark}">●</span> v_{x0} &nbsp; <span style="color:${theme.accel}">●</span> a_x·t &nbsp; <span style="color:${theme.primary}">●</span> v_x(t)`
        : `<span style="color:${theme.primaryDark}">●</span> v_{y0} &nbsp; <span style="color:${theme.accel}">●</span> a_y·t &nbsp; <span style="color:${theme.primary}">●</span> v_y(t)`;
    else if (getKinematicEquation() === "eq2")
      legend.innerHTML = horizMode
        ? `<span style="color:rgba(46,125,50,0.8)">■</span> v_{x0}·t &nbsp; <span style="color:rgba(46,125,50,0.6)">▲</span> 1/2 a_x t^2 &nbsp; <span style="color:${theme.primary}">—</span> v_x(t)`
        : `<span style="color:rgba(46,125,50,0.8)">■</span> v_{y0}·t &nbsp; <span style="color:rgba(46,125,50,0.6)">▲</span> 1/2 a_y t^2 &nbsp; <span style="color:${theme.primary}">—</span> v_y(t)`;
    else legend.innerHTML = "";
  }
}

function hideCalculationPopup() {
  const p = document.getElementById("calcPopup");
  if (p) p.style.display = "none";
}

function showCalculationPopup(arg) {
  const popup = document.getElementById("calcPopup");
  if (!popup) return;
  // only show when active kinematic selected, preview is not 'all', and user enabled the checkbox
  const selVal =
    (document.getElementById("previewSelect") || {}).value || "current";
  const showCalcCheckbox = document.getElementById("showCalc");
  if (
    !activeKinematic ||
    selVal === "all" ||
    (showCalcCheckbox && !showCalcCheckbox.checked)
  ) {
    popup.style.display = "none";
    return;
  }
  // determine time (tsec) and initial state p0 and preview state s
  let tsec = 0;
  let s = null;
  if (typeof arg === "number") {
    tsec = arg;
    s = getPreviewState(tsec);
  } else if (arg && typeof arg === "object") {
    s = arg;
    tsec = s.t || s.tFlight || totalFlightTime || 0;
  } else {
    tsec = currentSimTime || 0;
    s = getPreviewState(tsec);
  }
  let p0 = getPhysics(0);
  if (
    (document.getElementById("previewSelect") || {}).value &&
    (document.getElementById("previewSelect").value || "").startsWith("p")
  ) {
    const idx = parseInt(
      (document.getElementById("previewSelect").value || "").slice(1),
    );
    if (
      !isNaN(idx) &&
      savedPaths[idx] &&
      savedPaths[idx].data &&
      savedPaths[idx].data.length
    )
      p0 = savedPaths[idx].data[0];
  }
  const horizMode = !!(
    document.getElementById("horizontalMode") &&
    document.getElementById("horizontalMode").checked
  );
  // determine initial components and accelerations from p0 (or defaults)
  const vx0 = p0.vx || 0,
    vy0 = p0.vy || 0;
  const axFromP0 = p0 && p0.ax !== undefined ? p0.ax : getPhysics(0).ax || 0;
  const ayFromP0 =
    p0 && p0.ay !== undefined ? p0.ay : -(p0.g || getPhysics(0).g || 9.81);
  // For horizontal-only mode, y-components are zero and ay should be 0
  const ax = horizMode ? axFromP0 : 0;
  const ay = horizMode ? 0 : ayFromP0;
  // build LaTeX lines depending on active equation
  // build structured items: each item = {latex, type:'main'|'sub'|'final'}
  const items = [];
  if (activeKinematic === "eq2") {
    // For horizontal-only mode, compute x displacement and zero y
    const dx1 = vx0 * tsec;
    const dx2 = 0.5 * ax * tsec * tsec;
    const dx = dx1 + dx2;
    const dy = horizMode ? 0 : vy0 * tsec + 0.5 * ay * tsec * tsec;
    const sMag = Math.hypot(dx, dy);
    // s_x
    items.push({
      latex: `s_x = v_{x0} t + \\tfrac{1}{2} a_x t^{2}`,
      type: "main",
    });
    items.push({
      latex: `${vx0.toFixed(2)} \\times ${tsec.toFixed(2)} + \\tfrac{1}{2} \\times ${ax.toFixed(2)} \\times ${(tsec * tsec).toFixed(2)}`,
      type: "sub",
    });
    items.push({
      latex: `\\boxed{${dx.toFixed(2)}\\,\\mathrm{m}}`,
      type: "final",
    });
    // s_y (zero if horizontal-only)
    items.push({
      latex: `s_y = v_{y0} t + \\tfrac{1}{2} a_y t^{2}`,
      type: "main",
    });
    items.push({
      latex: `${horizMode ? 0 : vy0.toFixed(2)} \\times ${tsec.toFixed(2)} + \\tfrac{1}{2} \\times ${(horizMode ? 0 : ay).toFixed(2)} \\times ${(tsec * tsec).toFixed(2)}`,
      type: "sub",
    });
    items.push({
      latex: `\\boxed{${dy.toFixed(2)}\\,\\mathrm{m}}`,
      type: "final",
    });
    // magnitude
    items.push({ latex: `s = \\sqrt{s_x^{2} + s_y^{2}}`, type: "main" });
    items.push({
      latex: `\\boxed{${sMag.toFixed(2)}\\,\\mathrm{m}}`,
      type: "final",
    });
  } else if (activeKinematic === "eq1") {
    const vfx = vx0 + ax * tsec;
    const vfy = horizMode ? 0 : vy0 + ay * tsec;
    const vfmag = Math.hypot(vfx, vfy);
    items.push({ latex: `v_x = v_{x0} + a_x t`, type: "main" });
    items.push({
      latex: `${vx0.toFixed(2)} + ${ax.toFixed(2)} \\times ${tsec.toFixed(2)}`,
      type: "sub",
    });
    items.push({
      latex: `\\boxed{${vfx.toFixed(2)}\\,\\mathrm{m/s}}`,
      type: "final",
    });
    items.push({ latex: `v_y = v_{y0} + a_y t`, type: "main" });
    items.push({
      latex: `${horizMode ? 0 : vy0.toFixed(2)} + ${(horizMode ? 0 : ay).toFixed(2)} \\times ${tsec.toFixed(2)}`,
      type: "sub",
    });
    items.push({
      latex: `\\boxed{${vfy.toFixed(2)}\\,\\mathrm{m/s}}`,
      type: "final",
    });
    items.push({ latex: `v = \\sqrt{v_x^{2} + v_y^{2}}`, type: "main" });
    items.push({
      latex: `\\boxed{${vfmag.toFixed(2)}\\,\\mathrm{m/s}}`,
      type: "final",
    });
  }
  // render items with KaTeX, grouping main/sub/final styles
  popup.innerHTML = "";
  for (const it of items) {
    const el = document.createElement("div");
    el.className =
      "calc-line " +
      (it.type === "main" ? "main" : it.type === "sub" ? "sub" : "final");
    // ensure left alignment for KaTeX output by rendering inline-mode and letting parent handle alignment
    popup.appendChild(el);
    try {
      if (typeof katex !== "undefined")
        katex.render(it.latex, el, { throwOnError: false, displayMode: false });
      else el.textContent = it.latex;
    } catch (e) {
      el.textContent = it.latex;
    }
  }
  positionCalcPopup();
}

function drawScene(t) {
  ctx.clearRect(0, 0, W, H);
  const sel =
    (document.getElementById("previewSelect") || {}).value || "current";
  const horizMode = !!(
    document.getElementById("horizontalMode") &&
    document.getElementById("horizontalMode").checked
  );
  const isAll = sel === "all";
  const hideEqComponents =
    isOneDimensionalMotionDetected() && !!getKinematicEquation();
  // set owner for queued vectors: per-path owners will override inside loops
  try {
    currentVectorOwner = isAll ? "all" : "preview";
  } catch (e) {}

  // When previewing all paths, don't show equation UI artefacts
  if (isAll) {
    try {
      hideCalculationPopup();
    } catch (e) {}
    try {
      hideEquationGraph();
    } catch (e) {}
    try {
      const ov = document.getElementById("simulationResultsOverlay");
      if (ov) ov.style.display = "none";
    } catch (e) {}
  }

  // choose a base physics state for computing scale and cannon placement
  // ensure canvas size values exist (may not be set before a resize event)
  try {
    if (!W || !H) {
      const rect = document
        .getElementById("animationPane")
        .getBoundingClientRect();
      W = rect.width;
      H = rect.height - 60;
      canvas.width = W;
      canvas.height = H;
    }
  } catch (e) {}
  let baseH0 = getPhysics(0).h0;
  const focusEqVec =
    document.getElementById("focusEqVec") &&
    document.getElementById("focusEqVec").checked;
  // include visible saved paths initial heights so scale will fit all when previewing 'all'
  try {
    const visiblePaths = savedPaths.filter((p) => p.visible);
    if (visiblePaths.length)
      baseH0 = Math.max(
        ...visiblePaths.map((p) =>
          p.data && p.data.length ? p.data[0].h0 || 0 : 0,
        ),
        baseH0,
      );
  } catch (e) {}
  const defaultGroundY = H * 0.85;
  const groundY = defaultGroundY + (verticalOffset || 0);
  // scale must be based on the default layout so vertical panning only translates the view
  const scale = ((defaultGroundY - 50) / Math.max(80, baseH0)) * zoomLevel;
  const cannonX = W * 0.4;
  if (sel && sel.startsWith("p")) {
    const idx = parseInt(sel.slice(1));
    if (
      !isNaN(idx) &&
      savedPaths[idx] &&
      savedPaths[idx].data &&
      savedPaths[idx].data.length
    )
      baseH0 = savedPaths[idx].data[0].h0 || baseH0;
  }

  // when previewing an individual saved path or current, prepare its state
  const state = sel === "all" ? null : getPreviewState(t);

  // update instant display (when previewing single path/current)
  if (state) {
    if (!isDraggingSplitter) {
      document.getElementById("inst-x").textContent = state.x.toFixed(1);
      document.getElementById("inst-y").textContent = state.y.toFixed(1);
      document.getElementById("inst-vx").textContent = state.vx.toFixed(1);
      document.getElementById("inst-vy").textContent = state.vy.toFixed(1);
      // show acceleration components from the current state (handles horizontal-only ax)
      try {
        document.getElementById("inst-ax").textContent = (
          state.ax !== undefined ? state.ax : 0
        ).toFixed(1);
      } catch (e) {}
      try {
        document.getElementById("inst-ay").textContent = (
          state.ay !== undefined ? state.ay : -state.g
        ).toFixed(1);
      } catch (e) {}
      updateTrackBall(state);
    }
  } else {
    if (!isDraggingSplitter) {
      document.getElementById("inst-x").textContent = "-";
      document.getElementById("inst-y").textContent = "-";
      document.getElementById("inst-vx").textContent = "-";
      document.getElementById("inst-vy").textContent = "-";
      try {
        document.getElementById("inst-ax").textContent = "-";
      } catch (e) {}
      document.getElementById("inst-ay").textContent = "-";
    }
  }
  // show live calculation popup if enabled and an equation is selected (updates during play and scrubbing)
  try {
    const showCalcCheckbox = document.getElementById("showCalc");
    const selVal =
      (document.getElementById("previewSelect") || {}).value || "current";
    if (
      activeKinematic &&
      showCalcCheckbox &&
      showCalcCheckbox.checked &&
      selVal !== "all"
    ) {
      try {
        showCalculationPopup(t);
      } catch (e) {}
    } else {
      try {
        hideCalculationPopup();
      } catch (e) {}
    }
  } catch (e) {}
  // Show/hide live calculation popup if user enabled it and an equation is active
  try {
    const calcEnabled = !!(
      document.getElementById("showCalc") &&
      document.getElementById("showCalc").checked
    );
    const selVal =
      (document.getElementById("previewSelect") || {}).value || "current";
    if (activeKinematic && calcEnabled && selVal !== "all") {
      showCalculationPopup(t);
    } else {
      hideCalculationPopup();
    }
  } catch (e) {}
  // Show/hide and render equation graph pane when an equation is selected (single-preview only)
  try {
    const selVal2 =
      (document.getElementById("previewSelect") || {}).value || "current";
    if (activeKinematic && selVal2 !== "all") {
      showEquationGraph();
      try {
        renderEquationGraph(t);
      } catch (e) {}
    } else {
      hideEquationGraph();
    }
  } catch (e) {}
  const mainTimerEl = document.getElementById("timerDisplay");
  if (mainTimerEl) mainTimerEl.textContent = t.toFixed(2) + "s";
  try {
    updateScrubberUI(t);
  } catch (e) {}
  ctx.save();
  ctx.translate(offsetX, 0);
  // reset per-frame label/callout registries to avoid overlaps
  __currentLabelBoxes = [];
  __currentCalloutBoxes = [];

  if (document.getElementById("showGrid").checked) {
    ctx.strokeStyle = "#cfe2f3";
    for (let x = Math.floor(-offsetX / 40) * 40; x < -offsetX + W; x += 40) {
      ctx.beginPath();
      ctx.moveTo(x, 0);
      ctx.lineTo(x, groundY);
      ctx.stroke();
    }
    for (let y = 0; y < groundY; y += 40) {
      ctx.beginPath();
      ctx.moveTo(-offsetX, y);
      ctx.lineTo(-offsetX + W, y);
      ctx.stroke();
    }
  }

  // Environment theme colors
  const theme = getEnvTheme();
  // apply CSS variables for UI elements
  try {
    document.documentElement.style.setProperty("--env-sky", theme.sky);
    document.documentElement.style.setProperty(
      "--env-sky-light",
      theme.skyLight,
    );
    document.documentElement.style.setProperty(
      "--env-btn-active",
      theme.btnActive,
    );
  } catch (e) {}
  ctx.fillStyle = theme.ground;
  ctx.fillRect(-offsetX, groundY, W, H - groundY);
  if (theme.drawGrass) ctx.fillStyle = theme.grass;
  else ctx.fillStyle = "rgba(0,0,0,0)";
  ctx.fillRect(-offsetX, groundY, W, 8);
  // Draw launcher/building behind objects and vectors only when enabled
  try {
    const showBuilding = document.getElementById("showBuilding");
    if (!showBuilding || showBuilding.checked) {
      ctx.fillStyle = "#CFD8DC";
      ctx.fillRect(cannonX - 20, groundY - baseH0 * scale, 40, baseH0 * scale);
    }
  } catch (e) {
    ctx.fillStyle = "#CFD8DC";
    ctx.fillRect(cannonX - 20, groundY - baseH0 * scale, 40, baseH0 * scale);
  }

  // draw saved paths as background dots
  savedPaths.forEach((p) => {
    if (p.visible) {
      ctx.fillStyle = p.color;
      p.data.forEach((pt) => {
        ctx.beginPath();
        ctx.arc(
          cannonX + pt.x * scale * 0.5,
          groundY - pt.y * scale,
          1.5,
          0,
          7,
        );
        ctx.fill();
      });
    }
  });

  // When previewing all paths, also show the current (unsaved) path as faint dots
  if (isAll) {
    try {
      const curColor = getEnvTheme().primary || "#1976D2";
      ctx.fillStyle = curColor.indexOf("#") === 0 ? curColor : "#1976D2";
      // draw the current trajectory sample points
      for (
        let tt = 0;
        tt <= totalFlightTime;
        tt += Math.max(0.05, totalFlightTime / 200)
      ) {
        const s = getPhysics(tt);
        ctx.beginPath();
        ctx.arc(
          cannonX + s.x * scale * 0.5,
          groundY - s.y * scale,
          1.2,
          0,
          Math.PI * 2,
        );
        ctx.fill();
      }
    } catch (e) {}
  }

  if (sel === "all") {
    // animate a ball for each visible saved path
    savedPaths.forEach((p, idx) => {
      // tag vectors from this saved path so their shift cache is kept separate
      try {
        currentVectorOwner = "p" + idx;
      } catch (e) {}
      if (!p.visible) return;
      const s = samplePathStateAt(p, t);
      if (!s) return;
      const bx = cannonX + s.x * scale * 0.5,
        by = groundY - s.y * scale;
      // vectors per path if enabled
      if (document.getElementById("showTangent").checked && s.v_res > 0) {
        const angle = Math.atan2(-s.vy, s.vx);
        const tLen = 2000;
        ctx.strokeStyle = "rgba(0,0,0,0.3)";
        ctx.setLineDash([10, 10]);
        ctx.beginPath();
        ctx.moveTo(bx - Math.cos(angle) * tLen, by - Math.sin(angle) * tLen);
        ctx.lineTo(bx + Math.cos(angle) * tLen, by + Math.sin(angle) * tLen);
        ctx.stroke();
        ctx.setLineDash([]);
      }
      if (document.getElementById("velVec").checked) {
        const mode = document.getElementById("vectorMode").value,
          vs = vectorScale;
        const hideEqComponents =
          isOneDimensionalMotionDetected() && !!getKinematicEquation();
        if (mode === "all" || mode === "resultant")
          drawArrow(ctx, bx, by, s.vx * vs, -s.vy * vs, theme.primary, "v");
        if (!hideEqComponents) {
          if (mode === "all" || mode === "horizontal" || mode === "components")
            drawArrow(
              ctx,
              bx,
              by,
              s.vx * vs,
              0,
              theme.primaryRGBA || theme.primary,
              "vx",
            );
          if (mode === "all" || mode === "vertical" || mode === "components")
            drawArrow(
              ctx,
              bx,
              by,
              0,
              -s.vy * vs,
              theme.primaryRGBA || theme.primary,
              "vy",
            );
        }
      }
      if (document.getElementById("accelVec").checked) {
        const aScale = (vectorScale / 2.5) * 3;
        const ax = s.ax !== undefined ? s.ax : 0;
        const ay = s.ay !== undefined ? s.ay : -s.g;
        drawArrow(
          ctx,
          bx,
          by,
          ax * aScale,
          -ay * aScale,
          theme.accelRGBA || theme.accel,
          "a",
        );
      }
      // If kinematic equation 1 is enabled, show v = v0 + a·t decomposition
      // Only draw equation vectors when previewing a single path (not when showing all saved paths)
      if (getKinematicEquation() === "eq1" && sel !== "all") {
        try {
          const p0 = p.data && p.data.length ? p.data[0] : null;
          const vx0 = p0 ? p0.vx || 0 : 0;
          const vy0 = p0 ? p0.vy || 0 : 0;
          const tsec = s.t;
          const vs = vectorScale;
          // use full acceleration components (saved path state) so horizontal accel is drawn during horizontal-only mode
          const ax0 = s.ax !== undefined ? s.ax : 0;
          const ay0 = s.ay !== undefined ? s.ay : -s.g;
          const at_dx = ax0 * tsec;
          const at_dy = ay0 * tsec;
          const at_pixels_x = at_dx * vs;
          const at_pixels_y = -at_dy * vs; // convert to canvas dy
          // draw initial velocity vector anchored at projectile
          drawArrow(
            ctx,
            bx,
            by,
            vx0 * vs,
            -vy0 * vs,
            theme.primaryRGBA || theme.primary,
            "v0",
            true,
          );
          // draw a·t vector from the tip of v0 (uses both components)
          drawArrow(
            ctx,
            bx + vx0 * vs,
            by - vy0 * vs,
            at_pixels_x,
            at_pixels_y,
            theme.accelRGBA || theme.accel,
            "a·t",
            true,
          );
          // resultant from projectile center to tip of final velocity (v0 + a·t)
          const final_vx = vx0 + at_dx;
          const final_vy = vy0 + at_dy;
          const mode = document.getElementById("vectorMode").value;
          if (mode === "all" || mode === "resultant") {
            drawArrow(ctx, bx, by, final_vx * vs, -final_vy * vs, "blue", "v");
          }
        } catch (e) {}
      }
      {
        // Position vectors are independent from kinematic equation selection.
        const posOn =
          document.getElementById("posVec") &&
          document.getElementById("posVec").checked;
        const isEq2 = getKinematicEquation() === "eq2";
        // Only draw equation decomposition (isEq2) when previewing a single path
        if (posOn || (isEq2 && sel !== "all")) {
          // Decompose displacement: Δx = v0*t + 1/2*a*t^2
          const p0 = p.data && p.data.length ? p.data[0] : null;
          const h0 = p0 ? p0.h0 || 0 : 0;
          const originX = cannonX + 0 * scale * 0.5;
          const originY = groundY - h0 * scale;
          const vx0 = p0 ? p0.vx || 0 : 0;
          const vy0 = p0 ? p0.vy || 0 : 0;
          const ax = s.ax !== undefined ? s.ax : 0;
          const ay = s.ay !== undefined ? s.ay : -s.g;
          const tsec = s.t;
          // meters displacement components
          const dx1m = vx0 * tsec;
          const dy1m = vy0 * tsec;
          const dx2m = 0.5 * ax * tsec * tsec;
          const dy2m = 0.5 * ay * tsec * tsec;
          const dx1 = dx1m * scale * 0.5;
          const dy1 = -dy1m * scale;
          const dx2 = dx2m * scale * 0.5;
          const dy2 = -dy2m * scale;
          const mode = document.getElementById("vectorMode").value;
          const dxr = dx1 + dx2;
          const dyr = dy1 + dy2;
          const hideEqComponents =
            isOneDimensionalMotionDetected() && !!getKinematicEquation();

          if (mode === "all") {
            // Show equation decomposition (v0*t and 1/2 a·t^2) when eq2 is selected
            if (isEq2 && sel !== "all") {
              drawArrow(
                ctx,
                originX,
                originY,
                dx1,
                dy1,
                theme.displacementRGBA || theme.displacement,
                "v₀·t",
                true,
              );
              drawArrow(
                ctx,
                originX + dx1,
                originY + dy1,
                dx2,
                dy2,
                theme.displacementRGBALight || theme.displacement,
                "½ a·t²",
                true,
              );
            }
            // If user enabled position vectors, show Δx/Δy components as well (hidden when 1D+equation)
            if (posOn && !hideEqComponents) {
              const horizMode =
                !!(
                  document.getElementById("horizontalMode") &&
                  document.getElementById("horizontalMode").checked
                ) ||
                (Math.abs(ay) < 1e-9 && Math.abs(s.vy) < 1e-9);
              const isEq2Local =
                getKinematicEquation() === "eq2" && sel !== "all";
              if (!hideEqComponents)
                drawArrow(
                  ctx,
                  originX,
                  originY,
                  dxr,
                  0,
                  "rgba(46,125,50,0.6)",
                  "Δx",
                  isEq2Local,
                );
              if (!horizMode && !hideEqComponents)
                drawArrow(
                  ctx,
                  originX + dxr,
                  originY,
                  0,
                  dyr,
                  "rgba(46,125,50,0.6)",
                  "Δy",
                  isEq2Local,
                );
            }
            // resultant (prefer marking as equation vector when eq2 active)
            drawArrow(
              ctx,
              originX,
              originY,
              dxr,
              dyr,
              theme.displacement || "#2e7d32",
              "s",
              isEq2 && sel !== "all",
            );
          } else if (
            mode === "components" ||
            mode === "horizontal" ||
            mode === "vertical"
          ) {
            if (posOn && !hideEqComponents) {
              const isEq2Local =
                getKinematicEquation() === "eq2" && sel !== "all";
              if (mode !== "vertical" && !hideEqComponents)
                drawArrow(
                  ctx,
                  originX,
                  originY,
                  dxr,
                  0,
                  "rgba(46,125,50,0.6)",
                  "Δx",
                  isEq2Local,
                );
              if (mode !== "horizontal" && !hideEqComponents)
                drawArrow(
                  ctx,
                  originX + dxr,
                  originY,
                  0,
                  dyr,
                  "rgba(46,125,50,0.6)",
                  "Δy",
                  isEq2Local,
                );
            }
          } else if (mode === "resultant") {
            if (posOn || isEq2)
              drawArrow(ctx, originX, originY, dxr, dyr, "#2e7d32", "s", isEq2);
          }
        }
      }

      drawSelectedObject(ctx, bx, by, p.color || "orange", 8);
    });
  } else if (state) {
    const bx = cannonX + state.x * scale * 0.5,
      by = groundY - state.y * scale;
    if (document.getElementById("motionDiagram").checked) {
      ctx.fillStyle = theme.primary;
      for (let i = 0; i <= t; i += 0.1) {
        let s = getPreviewState(i);
        ctx.beginPath();
        ctx.arc(cannonX + s.x * scale * 0.5, groundY - s.y * scale, 1.5, 0, 7);
        ctx.fill();
      }
    }
    if (document.getElementById("showTangent").checked && state.v_res > 0) {
      const angle = Math.atan2(-state.vy, state.vx);
      const tLen = 2000;
      ctx.strokeStyle = "rgba(0,0,0,0.3)";
      ctx.setLineDash([10, 10]);
      ctx.beginPath();
      ctx.moveTo(bx - Math.cos(angle) * tLen, by - Math.sin(angle) * tLen);
      ctx.lineTo(bx + Math.cos(angle) * tLen, by + Math.sin(angle) * tLen);
      ctx.stroke();
      ctx.setLineDash([]);
    }

    if (document.getElementById("velVec").checked) {
      const mode = document.getElementById("vectorMode").value,
        vs = vectorScale;
      const hideEqComponents =
        isOneDimensionalMotionDetected() && !!getKinematicEquation();
      // For 'all', show both resultant and components (components hidden when 1D+equation)
      if (mode === "all" || mode === "resultant")
        drawArrow(
          ctx,
          bx,
          by,
          state.vx * vs,
          -state.vy * vs,
          theme.primary,
          "v",
        );
      if (!hideEqComponents) {
        if (mode === "all" || mode === "horizontal" || mode === "components")
          drawArrow(
            ctx,
            bx,
            by,
            state.vx * vs,
            0,
            theme.primaryRGBA || theme.primary,
            "vx",
          );
        if (mode === "all" || mode === "vertical" || mode === "components")
          drawArrow(
            ctx,
            bx,
            by,
            0,
            -state.vy * vs,
            theme.primaryRGBA || theme.primary,
            "vy",
          );
      }
    }
    if (document.getElementById("accelVec").checked) {
      const aScale = (vectorScale / 2.5) * 3;
      const ax = state.ax !== undefined ? state.ax : 0;
      const ay = state.ay !== undefined ? state.ay : -state.g;
      // draw acceleration vector using state components so horizontal-only mode shows horizontal accel
      drawArrow(
        ctx,
        bx,
        by,
        ax * aScale,
        -ay * aScale,
        theme.accelRGBA || theme.accel,
        "a",
      );
    }
    // If kinematic equation 1 is enabled, show v = v0 + a·t decomposition for current preview
    if (getKinematicEquation() === "eq1") {
      try {
        const previewSel =
          (document.getElementById("previewSelect") || {}).value || "current";
        let p0 = null;
        if (previewSel.startsWith("p")) {
          const idx = parseInt(previewSel.slice(1));
          if (
            !isNaN(idx) &&
            savedPaths[idx] &&
            savedPaths[idx].data &&
            savedPaths[idx].data.length
          )
            p0 = savedPaths[idx].data[0];
        }
        if (!p0) p0 = getPhysics(0);
        const vx0 = p0.vx || 0;
        const vy0 = p0.vy || 0;
        const tsec = state.t;
        const vs = vectorScale;
        // use initial-state acceleration components (fall back to state) so a·t is vectorial
        const ax0 =
          p0 && p0.ax !== undefined
            ? p0.ax
            : state.ax !== undefined
              ? state.ax
              : 0;
        const ay0 =
          p0 && p0.ay !== undefined
            ? p0.ay
            : state.ay !== undefined
              ? state.ay
              : -(state.g || p0.g || 9.81);
        const at_dx = ax0 * tsec;
        const at_dy = ay0 * tsec;
        const at_pixels_x = at_dx * vs;
        const at_pixels_y = -at_dy * vs;
        drawArrow(
          ctx,
          bx,
          by,
          vx0 * vs,
          -vy0 * vs,
          theme.primaryRGBA || theme.primary,
          "v0",
          true,
        );
        drawArrow(
          ctx,
          bx + vx0 * vs,
          by - vy0 * vs,
          at_pixels_x,
          at_pixels_y,
          theme.accelRGBA || theme.accel,
          "a·t",
          true,
        );
        const final_vx = vx0 + at_dx;
        const final_vy = vy0 + at_dy;
        const mode = document.getElementById("vectorMode").value;
        if (mode === "all" || mode === "resultant") {
          drawArrow(
            ctx,
            bx,
            by,
            final_vx * vs,
            -final_vy * vs,
            "blue",
            "v",
            true,
          );
        }
      } catch (e) {}
    }

    {
      // Position vectors are independent from kinematic equation selection for current preview.
      const posOn =
        document.getElementById("posVec") &&
        document.getElementById("posVec").checked;
      const isEq2 = getKinematicEquation() === "eq2";
      if (posOn || isEq2) {
        // For current preview, start at the initial launch position (h0)
        const previewSel =
          (document.getElementById("previewSelect") || {}).value || "current";
        let p0 = null;
        if (previewSel.startsWith("p")) {
          const idx = parseInt(previewSel.slice(1));
          if (
            !isNaN(idx) &&
            savedPaths[idx] &&
            savedPaths[idx].data &&
            savedPaths[idx].data.length
          )
            p0 = savedPaths[idx].data[0];
        }
        if (!p0) p0 = getPhysics(0);
        const h0 = p0.h0 || 0;
        const originX = cannonX + 0 * scale * 0.5;
        const originY = groundY - h0 * scale;
        const vx0 = p0.vx || 0;
        const vy0 = p0.vy || 0;
        const ax = state.ax !== undefined ? state.ax : 0;
        const ay = state.ay !== undefined ? state.ay : -getPhysics(0).g;
        const tsec = state.t;
        const dx1m = vx0 * tsec;
        const dy1m = vy0 * tsec;
        const dx2m = 0.5 * ax * tsec * tsec;
        const dy2m = 0.5 * ay * tsec * tsec;
        const dx1 = dx1m * scale * 0.5;
        const dy1 = -dy1m * scale;
        const dx2 = dx2m * scale * 0.5;
        const dy2 = -dy2m * scale;
        const dxr = dx1 + dx2;
        const dyr = dy1 + dy2;
        const mode = document.getElementById("vectorMode").value;
        const hideEqComponents =
          isOneDimensionalMotionDetected() && !!getKinematicEquation();
        if (mode === "all") {
          if (isEq2) {
            drawArrow(
              ctx,
              originX,
              originY,
              dx1,
              dy1,
              theme.displacementRGBA || theme.displacement,
              "v₀·t",
              true,
            );
            drawArrow(
              ctx,
              originX + dx1,
              originY + dy1,
              dx2,
              dy2,
              theme.displacementRGBALight || theme.displacement,
              "½ a·t²",
              true,
            );
          }
          if (posOn && !hideEqComponents) {
            const horizMode =
              !!(
                document.getElementById("horizontalMode") &&
                document.getElementById("horizontalMode").checked
              ) ||
              (Math.abs(ay) < 1e-9 && Math.abs(state.vy) < 1e-9);
            const isEq2Local =
              getKinematicEquation() === "eq2" && selVal2 !== "all";
            drawArrow(
              ctx,
              originX,
              originY,
              dxr,
              0,
              "rgba(46,125,50,0.6)",
              "Δx",
              isEq2Local,
            );
            if (!horizMode)
              drawArrow(
                ctx,
                originX + dxr,
                originY,
                0,
                dyr,
                "rgba(46,125,50,0.6)",
                "Δy",
                isEq2Local,
              );
          }
          drawArrow(ctx, originX, originY, dxr, dyr, "#2e7d32", "s", isEq2);
        } else if (
          mode === "components" ||
          mode === "horizontal" ||
          mode === "vertical"
        ) {
          if (posOn && !hideEqComponents) {
            if (mode !== "vertical")
              drawArrow(
                ctx,
                originX,
                originY,
                dxr,
                0,
                "rgba(46,125,50,0.6)",
                "Δx",
              );
            if (mode !== "horizontal")
              drawArrow(
                ctx,
                originX + dxr,
                originY,
                0,
                dyr,
                "rgba(46,125,50,0.6)",
                "Δy",
              );
          }
        } else if (mode === "resultant") {
          if (posOn || isEq2)
            drawArrow(ctx, originX, originY, dxr, dyr, "#2e7d32", "s", isEq2);
        }
      }
    }

    drawSelectedObject(ctx, bx, by, "orange", 8);
  }

  if (document.getElementById("showProbe").checked) {
    ctx.strokeStyle = "#ff5722";
    ctx.setLineDash([5, 5]);
    ctx.beginPath();
    ctx.moveTo(-offsetX, probeY);
    ctx.lineTo(W - offsetX, probeY);
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle = "#ff5722";
    ctx.fillRect(W - offsetX - 70, probeY - 12, 60, 24);
    ctx.fillStyle = "white";
    ctx.font = "bold 11px sans-serif";
    ctx.fillText(
      ((groundY - probeY) / scale).toFixed(1) + "m",
      W - offsetX - 65,
      probeY + 5,
    );
  }
  // calculation popup may be visible during animation when enabled
  // (do not forcibly hide during running)
  try {
    processPendingVectors();
  } catch (e) {}
  ctx.restore();
  updateCharts(t);
  // render queued vector labels into the overlay using KaTeX
  try {
    renderVectorLabels();
  } catch (e) {}
}

function renderVectorLabels() {
  const layer = document.getElementById("vectorLabelLayer");
  if (!layer) return;
  // clear previous labels
  layer.innerHTML = "";
  const crect = canvas.getBoundingClientRect();
  vectorLabelQueue.forEach((lbl, i) => {
    const el = document.createElement("div");
    el.className = "vector-label" + (lbl.isEq ? " eq" : "");
    el.style.left = lbl.x + (offsetX || 0) + "px";
    el.style.top = lbl.y + "px";
    el.style.color = lbl.color || "#111";
    // render LaTeX into element
    try {
      const latex = labelToLatex(lbl.text);
      katex.render(latex, el, { throwOnError: false, displayMode: false });
    } catch (e) {
      el.textContent = lbl.text;
    }
    layer.appendChild(el);
  });
  // reset queue
  vectorLabelQueue = [];
}

// Process queued vectors drawn to main canvas: detect overlap and apply shifts only when needed.
function processPendingVectors() {
  if (!pendingVectors || !pendingVectors.length) return;
  // If user enabled "Separate Overlapping Vectors" and the motion is 1-D,
  // apply a simple perpendicular offset per cluster to separate overlapping
  // arrows. Otherwise draw arrows exactly at their computed endpoints.
  try {
    const chk = document.getElementById("separateVectors");
    const separateEnabled = chk && chk.checked;
    const is1D = isOneDimensionalMotionDetected();
    if (separateEnabled && is1D) {
      const shiftVal =
        parseFloat((document.getElementById("vectorShift") || {}).value) || 0;
      const horiz = isHorizontalOnlyDetected();
      // cluster vectors by start position using a small pixel bucket so
      // nearly-overlapping vectors (like equation-derived arrows) group together.
      const clusters = {};
      const BUCKET_PX = 4; // group vectors within this many pixels
      const roundKey = (v) =>
        `${Math.round(v.x / BUCKET_PX)}|${Math.round(v.y / BUCKET_PX)}`;
      // label sets used for special kinematic grouping
      const eq1Labels = new Set(["v0", "a_t"]);
      const eq2Labels = new Set(["v0t", "half_at_t2"]);
      const componentLabels = new Set(["vx", "vy"]);
      const resultantLabels = new Set(["v", "a", "s"]);
      pendingVectors.forEach((v) => {
        const k = roundKey(v);
        (clusters[k] = clusters[k] || []).push(v);
      });
      // If an equation is active, force its equation vectors into a single synthetic cluster
      if (activeKinematic === "eq1" || activeKinematic === "eq2") {
        const target = activeKinematic === "eq1" ? eq1Labels : eq2Labels;
        const special = [];
        pendingVectors.forEach((v) => {
          if (target.has(canonicalLabel(v.label))) special.push(v);
        });
        if (special.length > 1) {
          const key = "__eq_special__";
          clusters[key] = special;
          // remove these vectors from their previous clusters to avoid duplicate draws
          Object.keys(clusters).forEach((k) => {
            if (k === key) return;
            clusters[k] = clusters[k].filter((v) => !special.includes(v));
            if (clusters[k].length === 0) delete clusters[k];
          });
        }
      }
      Object.values(clusters).forEach((group) => {
        // Identify vectors for this group
        const resultants = [];
        const shiftCandidates = [];
        const others = [];
        const specialEqVectors = new Set(["v0", "v0t", "a_t", "half_at_t2"]);
        // collect resultants first
        for (let i = 0; i < group.length; i++) {
          const vv = group[i];
          const cl = canonicalLabel(vv.label);
          if (resultantLabels.has(cl)) resultants.push(vv);
        }
        // collect shift candidates depending on active equation or fallback rules
        if (activeKinematic === "eq1" || activeKinematic === "eq2") {
          for (let i = 0; i < group.length; i++) {
            const vv = group[i];
            const cl = canonicalLabel(vv.label);
            if (resultantLabels.has(cl)) continue;
            // always include the special equation vectors as shift candidates
            if (specialEqVectors.has(cl) || vv.isEq) shiftCandidates.push(vv);
            else others.push(vv);
          }
        } else {
          for (let i = 0; i < group.length; i++) {
            const vv = group[i];
            const cl = canonicalLabel(vv.label);
            if (resultantLabels.has(cl)) continue;
            if (specialEqVectors.has(cl) || vv.isEq || componentLabels.has(cl))
              shiftCandidates.push(vv);
            else others.push(vv);
          }
        }
        // If there are no shift candidates and the group is singular, draw it normally
        if (shiftCandidates.length === 0 && group.length <= 1) {
          group.forEach((v) => {
            try {
              drawArrowImmediate(
                ctx,
                v.x,
                v.y,
                v.dx,
                v.dy,
                v.color,
                v.label,
                v.isEq,
              );
            } catch (e) {}
          });
          return;
        }
        // Draw all resultants at original positions (deterministic order)
        resultants.sort((A, B) => {
          const ka = makeVectorKey(A);
          const kb = makeVectorKey(B);
          if (ka < kb) return -1;
          if (ka > kb) return 1;
          return 0;
        });
        resultants.forEach((rv) => {
          try {
            drawArrowImmediate(
              ctx,
              rv.x,
              rv.y,
              rv.dx,
              rv.dy,
              rv.color,
              rv.label,
              rv.isEq,
            );
          } catch (e) {}
        });
        // Draw other non-shifted vectors at original positions
        others.sort((A, B) => {
          const ka = makeVectorKey(A);
          const kb = makeVectorKey(B);
          if (ka < kb) return -1;
          if (ka > kb) return 1;
          return 0;
        });
        others.forEach((o) => {
          try {
            drawArrowImmediate(
              ctx,
              o.x,
              o.y,
              o.dx,
              o.dy,
              o.color,
              o.label,
              o.isEq,
            );
          } catch (e) {}
        });
        // Shift only the shiftCandidates; all shifted in same perpendicular direction
        shiftCandidates.sort((a, b) => {
          const ka = makeVectorKey(a);
          const kb = makeVectorKey(b);
          if (ka < kb) return -1;
          if (ka > kb) return 1;
          return 0;
        });
        for (let i = 0; i < shiftCandidates.length; i++) {
          const v = shiftCandidates[i];
          const off = (i + 1) * shiftVal; // all same direction and increasing offset
          let sx = v.x,
            sy = v.y;
          if (horiz) sy += off;
          else sx += off;
          try {
            drawArrowImmediate(
              ctx,
              sx,
              sy,
              v.dx,
              v.dy,
              v.color,
              v.label,
              v.isEq,
            );
          } catch (e) {}
        }
      });
    } else {
      pendingVectors.forEach((v) => {
        try {
          drawArrowImmediate(
            ctx,
            v.x,
            v.y,
            v.dx,
            v.dy,
            v.color,
            v.label,
            v.isEq,
          );
        } catch (e) {}
      });
    }
  } catch (e) {
    // fallback: draw everything at computed endpoints
    pendingVectors.forEach((v) => {
      try {
        drawArrowImmediate(ctx, v.x, v.y, v.dx, v.dy, v.color, v.label, v.isEq);
      } catch (e) {}
    });
  }
  pendingVectors = [];
}

// Timescrubber helpers: render tick marks and update header/thumb positions
function getTickInterval(maxT) {
  if (maxT <= 5) return 0.5;
  if (maxT <= 10) return 1;
  if (maxT <= 30) return 2;
  // pick a round step roughly 8-12 ticks
  const approx = Math.ceil(maxT / 10);
  const pow = Math.pow(10, Math.floor(Math.log10(approx)));
  const nice = Math.ceil(approx / pow) * pow;
  return nice;
}

function renderScrubberTicks() {
  const ticksHolder = document.getElementById("scrubberTicks");
  const slider = document.getElementById("timeSlider");
  if (!ticksHolder || !slider) return;
  const maxT = parseFloat(slider.max) || 1;
  ticksHolder.innerHTML = "";
  const step = getTickInterval(maxT);
  const leftPad = 0;
  const rightPad = 0;
  for (let t = 0; t <= maxT + 1e-9; t += step) {
    const pct = (t / maxT) * 100;
    const tick = document.createElement("div");
    tick.className = "tick";
    tick.style.left = `calc(${pct}% )`;
    const lbl = document.createElement("div");
    lbl.className = "label";
    lbl.textContent = t % 1 === 0 ? `${t.toFixed(0)}s` : `${t.toFixed(1)}s`;
    tick.appendChild(lbl);
    tick.addEventListener("click", (e) => {
      e.stopPropagation();
      slider.value = t;
      slider.dispatchEvent(new Event("input"));
      slider.dispatchEvent(new Event("change"));
    });
    ticksHolder.appendChild(tick);
  }
}

function updateScrubberUI(t) {
  const slider = document.getElementById("timeSlider");
  const thumb = document.getElementById("scrubberThumbTime");
  if (!slider) return;
  const maxT = parseFloat(slider.max) || 1;
  const pct = maxT <= 0 ? 0 : Math.min(Math.max(t, 0), maxT) / maxT;
  // position thumb pixel-perfect aligned with native slider thumb
  const sliderRect = slider.getBoundingClientRect();
  const parentRect = slider.parentElement.getBoundingClientRect();
  const thumbCenterX = sliderRect.left + pct * sliderRect.width;
  const leftPx = Math.min(
    Math.max(0, thumbCenterX - parentRect.left),
    parentRect.width,
  );
  if (thumb) {
    thumb.style.left = leftPx + "px";
    thumb.textContent = t.toFixed(2) + "s";
  }
  // keep main timerDisplay in sync for backward compatibility
  const mainTimer = document.getElementById("timerDisplay");
  if (mainTimer) mainTimer.textContent = t.toFixed(2) + "s";
}

// Confirmation dialog helpers
function ensureConfirmDialog() {
  if (document.getElementById("confirmBackdrop")) return;
  const bd = document.createElement("div");
  bd.id = "confirmBackdrop";
  bd.className = "dialog-backdrop";
  bd.innerHTML = `
        <div class="confirm-dialog" role="dialog" aria-modal="true">
            <h4 id="confirmTitle">Confirm</h4>
            <p id="confirmMessage">Are you sure?</p>
            <div class="confirm-actions">
                <button id="confirmCancel" class="confirm-btn cancel">No</button>
                <button id="confirmYes" class="confirm-btn yes">Yes</button>
            </div>
        </div>`;
  document.body.appendChild(bd);
  bd.querySelector("#confirmCancel").addEventListener("click", () => {
    hideConfirmDialog();
  });
  bd.querySelector("#confirmYes").addEventListener("click", () => {
    if (typeof bd.__yesCb === "function") bd.__yesCb();
    hideConfirmDialog();
  });
}

function showConfirmDialog(title, message, yesCb) {
  ensureConfirmDialog();
  const bd = document.getElementById("confirmBackdrop");
  if (!bd) return;
  bd.querySelector("#confirmTitle").textContent = title || "Confirm";
  bd.querySelector("#confirmMessage").textContent = message || "";
  bd.__yesCb = yesCb || null;
  bd.classList.add("show");
  // trap focus
  try {
    bd.querySelector("#confirmCancel").focus();
  } catch (e) {}
}

function hideConfirmDialog() {
  const bd = document.getElementById("confirmBackdrop");
  if (!bd) return;
  bd.classList.remove("show");
  bd.__yesCb = null;
}

function updateCharts(currentTime) {
  const showTan = document.getElementById("showTangent").checked;
  const theme = getEnvTheme();
  charts.forEach((chart, idx) => {
    const type = chartTypes[idx];
    const sNow = getPhysics(currentTime);

    // Dynamic Datasets: Current Path (Index 0) + Saved Paths
    let datasets = [];

    // 1. Current Active Path
    let currentPathData = [];
    for (let i = 0; i <= currentTime; i += 0.05) {
      let s = getPhysics(i);
      currentPathData.push({
        x: i,
        y:
          type === "y"
            ? s.y
            : type === "vy"
              ? s.vy
              : type === "ay"
                ? s.ay
                : type === "ax"
                  ? s.ax
                  : type === "x"
                    ? s.x
                    : type === "vx"
                      ? s.vx
                      : s.v_res,
      });
    }
    datasets.push({
      label: "Current",
      showLine: true,
      data: currentPathData,
      borderColor: theme.primary,
      pointRadius: 0,
      borderWidth: 3,
    });

    // If equation 2 is active, add a filled area under the velocity curves (vx/vy) up to currentTime
    try {
      if (
        typeof activeKinematic !== "undefined" &&
        activeKinematic === "eq2" &&
        (type === "vy" || type === "vx")
      ) {
        // build filled data that contains the same x points but y only up to currentTime
        const filled = [];
        for (let t = 0; t <= currentTime; t += 0.05) {
          const s = getPhysics(t);
          const val = type === "vy" ? s.vy : s.vx;
          filled.push({ x: t, y: val });
        }
        // close the area back to zero to create a fill down to x-axis
        const lastT = filled.length ? filled[filled.length - 1].x : 0;
        filled.push({ x: lastT, y: 0 });
        filled.unshift({ x: 0, y: 0 });
        datasets.push({
          label: "Displacement (area)",
          data: filled,
          fill: true,
          backgroundColor: theme.displacementFill || "rgba(46,125,50,0.12)",
          borderColor: theme.displacementRGBA || "rgba(46,125,50,0.6)",
          pointRadius: 0,
          borderWidth: 0.5,
          showLine: true,
        });
      }
    } catch (e) {}

    // 2. Saved Paths
    savedPaths.forEach((path, pIdx) => {
      if (path.visible) {
        let savedData = path.data.map((p) => ({
          x: p.t,
          y:
            type === "y"
              ? p.y
              : type === "vy"
                ? p.vy
                : type === "ay"
                  ? p.ay
                  : type === "ax"
                    ? p.ax
                    : type === "x"
                      ? p.x
                      : type === "vx"
                        ? p.vx
                        : p.v_res,
        }));
        datasets.push({
          label: `Path ${pIdx + 1}`,
          showLine: true,
          data: savedData,
          borderColor: path.color,
          pointRadius: 0,
          borderWidth: 1.5,
        });
      }
    });

    chart.data.datasets = datasets;
    let maxFlight = Math.max(
      2,
      sNow.tFlight,
      ...savedPaths.map((p) => p.tFlight),
    );
    chart.options.scales.x.max = maxFlight;

    if (showTan) {
      let val =
        type === "y"
          ? sNow.y
          : type === "vy"
            ? sNow.vy
            : type === "ay"
              ? sNow.ay
              : type === "ax"
                ? sNow.ax
                : type === "x"
                  ? sNow.x
                  : type === "vx"
                    ? sNow.vx
                    : sNow.v_res;
      let slope =
        type === "y"
          ? sNow.vy
          : type === "vy"
            ? sNow.ay
            : type === "ay"
              ? 0
              : type === "ax"
                ? 0
                : type === "x"
                  ? sNow.vx
                  : type === "vx"
                    ? 0
                    : sNow.v_res > 0
                      ? (sNow.ay * sNow.vy) / sNow.v_res
                      : 0;
      chart.options.plugins.annotation.annotations = {
        tangent: {
          type: "line",
          xMin: currentTime - 0.4,
          xMax: currentTime + 0.4,
          yMin: val - slope * 0.4,
          yMax: val + slope * 0.4,
          borderColor: "rgba(255, 87, 34, 0.8)",
          borderWidth: 2,
          borderDash: [4, 4],
        },
      };
    } else {
      chart.options.plugins.annotation.annotations = {};
    }
    chart.update("none");
  });
}

// Draw the selected object at canvas coords (x,y).
function drawSelectedObject(ctx, x, y, color, size) {
  const type = (document.getElementById("objectType") || {}).value || "ball";
  // Increase render size for ball/person/car while keeping 'size' as a base unit.
  ctx.save();
  ctx.translate(x, y);
  if (type === "point") {
    const r = Math.max(3, size * 0.5);
    ctx.fillStyle = color || "black";
    ctx.beginPath();
    ctx.arc(0, 0, r, 0, Math.PI * 2);
    ctx.fill();
  } else if (type === "ball") {
    const r = Math.max(6, Math.round(size * 1.8));
    ctx.fillStyle = color || "orange";
    ctx.beginPath();
    ctx.arc(0, 0, r, 0, Math.PI * 2);
    ctx.fill();
    ctx.strokeStyle = "#333";
    ctx.lineWidth = 1.5;
    ctx.stroke();
  } else if (type === "car") {
    // larger car: body + two wheels
    const w = Math.max(28, Math.round(size * 4.0));
    const h = Math.max(12, Math.round(size * 1.6));
    ctx.fillStyle = color || "#1976d2";
    ctx.beginPath();
    ctx.rect(-w / 2, -h, w, h);
    ctx.fill();
    ctx.fillStyle = "#222";
    ctx.beginPath();
    ctx.arc(-w * 0.25, 0, Math.max(6, Math.round(size * 0.9)), 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(w * 0.25, 0, Math.max(6, Math.round(size * 0.9)), 0, Math.PI * 2);
    ctx.fill();
  } else if (type === "person") {
    // more solid person figure (not stickman): head + torso + limbs
    const headR = Math.max(8, Math.round(size * 1.0));
    const torsoW = Math.max(12, Math.round(size * 1.6));
    const torsoH = Math.max(18, Math.round(size * 2.4));
    const armW = Math.max(6, Math.round(size * 0.6));
    const legW = Math.max(6, Math.round(size * 0.7));
    const headY = -torsoH - headR + 6;
    // head
    ctx.fillStyle = color || "#2e7d32";
    ctx.beginPath();
    ctx.arc(0, headY, headR, 0, Math.PI * 2);
    ctx.fill();
    // torso
    ctx.fillRect(-torsoW / 2, -torsoH, torsoW, torsoH);
    // arms
    ctx.fillRect(-torsoW / 2 - armW, -torsoH + 6, armW, torsoH - 6);
    ctx.fillRect(torsoW / 2, -torsoH + 6, armW, torsoH - 6);
    // legs
    ctx.fillRect(-torsoW / 4 - legW / 2, 0, legW, torsoH / 1.2);
    ctx.fillRect(torsoW / 4 - legW / 2, 0, legW, torsoH / 1.2);
  }
  ctx.restore();
}

// Zoom helper functions and input handlers
function updateZoomDisplay() {
  const pct = Math.round(zoomLevel * 100);
  const el = document.getElementById("zoomPct");
  if (el) el.textContent = pct + "%";
  const slider = document.getElementById("zoomSlider");
  if (slider) slider.value = pct;
}

function zoomTo(factor, centerX) {
  const rect = canvas.getBoundingClientRect();
  const cx = typeof centerX === "number" ? centerX : rect.width / 2;
  const newZoom = Math.min(ZOOM_MAX, Math.max(ZOOM_MIN, zoomLevel * factor));
  offsetX = cx - (cx - offsetX) * (newZoom / zoomLevel);
  zoomLevel = newZoom;
  updateZoomDisplay();
  drawScene(currentSimTime);
}

function zoomIn() {
  zoomTo(ZOOM_STEP);
}
function zoomOut() {
  zoomTo(1 / ZOOM_STEP);
}
function zoomReset() {
  zoomLevel = 1;
  offsetX = 0;
  updateZoomDisplay();
  drawScene(currentSimTime);
}

// Wheel / trackpad gestures: two-finger horizontal pan, pinch-to-zoom, ignore vertical scroll
canvas.addEventListener(
  "wheel",
  (e) => {
    // We'll handle three cases:
    // 1) horizontal scroll (deltaX dominant) -> pan the view
    // 2) pinch-to-zoom from trackpad (often arrives as wheel with ctrl/meta pressed or large vertical delta) -> zoom
    // 3) vertical scroll (deltaY dominant) -> do nothing (prevent default so canvas doesn't scroll the page)
    const rect = canvas.getBoundingClientRect();
    const absX = Math.abs(e.deltaX);
    const absY = Math.abs(e.deltaY);
    // Case 1: horizontal two-finger pan
    if (absX > absY && absX > 0.5) {
      e.preventDefault();
      // pan in the same direction as the finger movement (deltaX positive => user moved fingers left->right, so move content left)
      offsetX -= e.deltaX;
      drawScene(currentSimTime);
      return;
    }

    // Case 2: pinch-to-zoom detection: ctrl/meta pressed or vertical delta larger but likely from pinch
    const isCtrl = e.ctrlKey || e.metaKey;
    if (isCtrl || (absY > absX && absY > 0.5)) {
      e.preventDefault();
      const mouseX = e.clientX - rect.left;
      // Use an exponential mapping so pinch amount scales smoothly with deltaY
      const sensitivity = 0.0016; // tuned for trackpad wheel deltas
      const factor = Math.exp(-e.deltaY * sensitivity);
      const newZoom = Math.min(
        ZOOM_MAX,
        Math.max(ZOOM_MIN, zoomLevel * factor),
      );
      offsetX = mouseX - (mouseX - offsetX) * (newZoom / zoomLevel);
      zoomLevel = newZoom;
      updateZoomDisplay();
      drawScene(currentSimTime);
      return;
    }

    // Case 3: vertical two-finger scroll -> do nothing (prevent page scrolling when over canvas)
    if (absY > absX) {
      e.preventDefault();
      return;
    }
  },
  { passive: false },
);

// Touch gesture handling: distinguish two-finger horizontal pan vs pinch-to-zoom
let touchGesture = { mode: null, prevDist: null, prevMid: null };
canvas.addEventListener(
  "touchstart",
  (e) => {
    if (e.touches.length === 2) {
      const dx = e.touches[0].clientX - e.touches[1].clientX;
      const dy = e.touches[0].clientY - e.touches[1].clientY;
      touchGesture.prevDist = Math.hypot(dx, dy);
      touchGesture.prevMid = {
        x: (e.touches[0].clientX + e.touches[1].clientX) / 2,
        y: (e.touches[0].clientY + e.touches[1].clientY) / 2,
      };
      touchGesture.mode = null; // undecided until movement
    }
  },
  { passive: true },
);

canvas.addEventListener(
  "touchmove",
  (e) => {
    if (e.touches.length !== 2 || !touchGesture.prevDist) return;
    // decide gesture mode based on relative change in distance vs midpoint translation
    const dx = e.touches[0].clientX - e.touches[1].clientX;
    const dy = e.touches[0].clientY - e.touches[1].clientY;
    const dist = Math.hypot(dx, dy);
    const mid = {
      x: (e.touches[0].clientX + e.touches[1].clientX) / 2,
      y: (e.touches[0].clientY + e.touches[1].clientY) / 2,
    };
    const deltaMidX =
      mid.x - ((touchGesture.prevMid && touchGesture.prevMid.x) || mid.x);
    const deltaMidY =
      mid.y - ((touchGesture.prevMid && touchGesture.prevMid.y) || mid.y);
    const distDelta = Math.abs(dist - touchGesture.prevDist);
    // thresholds (in pixels)
    const PINCH_THRESHOLD = 6; // treat as pinch if distance changes more than this
    const PAN_THRESHOLD = 6; // treat as pan if midpoint moves more than this horizontally relative to vertical

    if (!touchGesture.mode) {
      if (distDelta > PINCH_THRESHOLD && distDelta > Math.abs(deltaMidX))
        touchGesture.mode = "pinch";
      else if (
        Math.abs(deltaMidX) > PAN_THRESHOLD &&
        Math.abs(deltaMidX) > Math.abs(deltaMidY)
      )
        touchGesture.mode = "pan";
      else {
        // not enough movement to decide yet
        touchGesture.prevDist = dist;
        touchGesture.prevMid = mid;
        return;
      }
    }

    if (touchGesture.mode === "pinch") {
      // pinch -> zoom
      e.preventDefault();
      const rect = canvas.getBoundingClientRect();
      const midX = mid.x - rect.left; // canvas-relative
      const factor = dist / touchGesture.prevDist;
      zoomTo(factor, midX);
      touchGesture.prevDist = dist;
      touchGesture.prevMid = mid;
    } else if (touchGesture.mode === "pan") {
      // two-finger horizontal pan -> translate offsetX
      e.preventDefault();
      // only use horizontal component
      offsetX += deltaMidX;
      touchGesture.prevMid = mid;
      drawScene(currentSimTime);
    }
  },
  { passive: false },
);

canvas.addEventListener(
  "touchend",
  (e) => {
    if (e.touches.length < 2) {
      touchGesture.mode = null;
      touchGesture.prevDist = null;
      touchGesture.prevMid = null;
    }
  },
  { passive: true },
);

// Hook zoom slider UI
const zs = document.getElementById("zoomSlider");
if (zs) {
  zs.addEventListener("input", (e) => {
    const rect = canvas.getBoundingClientRect();
    const newZoom = parseFloat(e.target.value) / 100;
    const factor = newZoom / zoomLevel;
    zoomTo(factor, rect.width / 2);
  });
}
const zp = document.getElementById("zoomPct");
if (zp) zp.addEventListener("dblclick", zoomReset);
updateZoomDisplay();

// Toggle to show/hide the zoom bar when user clicks the scrubber button
const zoomToggleBtn = document.getElementById("zoomToggleBtn");
if (zoomToggleBtn) {
  zoomToggleBtn.addEventListener("click", () => {
    const zb = document.getElementById("zoomBar");
    if (!zb) return;
    if (zb.style.display === "none" || zb.style.display === "") {
      zb.style.display = "flex";
      // ensure slider reflects current zoom
      updateZoomDisplay();
      const s = document.getElementById("zoomSlider");
      if (s) s.focus();
    } else {
      zb.style.display = "none";
    }
  });
}

// Hook plus/minus/reset buttons
const zMinus = document.getElementById("zoomMinus");
if (zMinus)
  zMinus.addEventListener("click", () => {
    zoomTo(1 / ZOOM_STEP);
    updateZoomDisplay();
    const s = document.getElementById("zoomSlider");
    if (s) s.value = Math.round(zoomLevel * 100);
  });
const zPlus = document.getElementById("zoomPlus");
if (zPlus)
  zPlus.addEventListener("click", () => {
    zoomTo(ZOOM_STEP);
    updateZoomDisplay();
    const s = document.getElementById("zoomSlider");
    if (s) s.value = Math.round(zoomLevel * 100);
  });
const zResetBtn = document.getElementById("zoomResetBtn");
if (zResetBtn)
  zResetBtn.addEventListener("click", () => {
    zoomReset();
    updateZoomDisplay();
    const s = document.getElementById("zoomSlider");
    if (s) s.value = 100;
  });

canvas.onmousedown = (e) => {
  const rect = canvas.getBoundingClientRect();
  if (
    Math.abs(e.clientY - rect.top - probeY) < 15 &&
    document.getElementById("showProbe").checked
  ) {
    isDraggingProbe = true;
  } else {
    isPanning = true;
    panStartX = e.clientX;
    panStartY = e.clientY;
    panMode = null;
    // store originals to apply delta during drag
    panOrigOffsetX = offsetX;
    panOrigVerticalOffset = verticalOffset;
    canvas.classList.add("grabbing");
  }
};

window.onmousemove = (e) => {
  const rect = canvas.getBoundingClientRect();
  const mouseY = e.clientY - rect.top;

  const defaultGroundY = H * 0.85;
  const currentGroundY = defaultGroundY + (verticalOffset || 0);
  if (
    Math.abs(mouseY - probeY) < 15 &&
    document.getElementById("showProbe").checked
  ) {
    canvas.style.cursor = "ns-resize";
  } else {
    canvas.style.cursor = isPanning ? "grabbing" : "grab";
  }

  if (isDraggingProbe) {
    probeY = Math.max(20, Math.min(e.clientY - rect.top, currentGroundY));
    drawScene(currentSimTime);
  } else if (isPanning) {
    const dx = e.clientX - panStartX;
    const dy = e.clientY - panStartY;
    if (!panMode) {
      // decide pan direction after small threshold
      if (Math.abs(dx) > Math.abs(dy) && Math.abs(dx) > 4) panMode = "h";
      else if (Math.abs(dy) > 4) panMode = "v";
      else return;
    }
    if (panMode === "h") {
      offsetX = panOrigOffsetX + dx;
    } else if (panMode === "v") {
      // verticalOffset positive -> ground moves down (more ground visible)
      verticalOffset = panOrigVerticalOffset + dy;
      // clamp groundY so there's always some sky and some ground
      const minGroundY = 40;
      const maxGroundY = Math.max(H - 40, defaultGroundY);
      if (defaultGroundY + verticalOffset < minGroundY)
        verticalOffset = minGroundY - defaultGroundY;
      if (defaultGroundY + verticalOffset > maxGroundY)
        verticalOffset = maxGroundY - defaultGroundY;
    }
    drawScene(currentSimTime);
  }
};

window.onmouseup = () => {
  isDraggingProbe = false;
  isPanning = false;
  panMode = null;
  panOrigOffsetX = 0;
  panOrigVerticalOffset = 0;
  canvas.classList.remove("grabbing");
};

document.getElementById("start").onclick = () => {
  if (!running) {
    running = true;
    lastTimestamp = performance.now();
    document.getElementById("start").textContent = "⏸";
    // set flight time based on preview selection
    const sel = document.getElementById("previewSelect");
    if (sel && sel.value) {
      if (sel.value === "current") totalFlightTime = getPhysics(0).tFlight;
      else if (sel.value === "all")
        totalFlightTime = Math.max(
          getPhysics(0).tFlight,
          ...savedPaths.map((p) => p.tFlight || 0),
        );
      else {
        const idx = parseInt(sel.value.slice(1));
        if (!isNaN(idx) && savedPaths[idx])
          totalFlightTime = savedPaths[idx].tFlight;
        else totalFlightTime = getPhysics(0).tFlight;
      }
    } else {
      totalFlightTime = getPhysics(0).tFlight;
    }
    {
      const ts = document.getElementById("timeSlider");
      if (ts) {
        ts.max = totalFlightTime;
        ts.step = "any";
        ts.value = Math.min(parseFloat(ts.value) || 0, parseFloat(ts.max) || 0);
        try {
          renderScrubberTicks();
          updateScrubberUI(parseFloat(ts.value) || 0);
        } catch (e) {}
      }
    }
    requestAnimationFrame(loop);
    hideCalculationPopup();
  } else {
    running = false;
    document.getElementById("start").textContent = "▶";
  }
};

document.getElementById("reset").onclick = () => {
  running = false;
  currentSimTime = 0;
  offsetX = 0;
  verticalOffset = 0;
  document.getElementById("start").textContent = "▶";
  document.getElementById("timeSlider").value = 0;
  drawScene(0);
  document.getElementById("simulationResultsOverlay").style.display = "none";
  hideCalculationPopup();
};

document.getElementById("timeSlider").oninput = (e) => {
  currentSimTime = parseFloat(e.target.value);
  drawScene(currentSimTime);
  try {
    updateScrubberUI(currentSimTime);
  } catch (e) {}
  // update table values as user scrubs
  if (
    document.getElementById("pathTableContainer") &&
    document.getElementById("pathTableContainer").style.display !== "none"
  )
    renderPathTables();
  if (currentSimTime >= totalFlightTime - 0.01)
    showResults(getPreviewSummary());
  else {
    document.getElementById("simulationResultsOverlay").style.display =
      "none"; /* hide while scrubbing; will show on release */
  }
};

// Show calculations when user finishes scrubbing (change / pointerup / touchend)
const timeSliderEl = document.getElementById("timeSlider");
if (timeSliderEl) {
  timeSliderEl.addEventListener("change", () => {
    if (
      document.getElementById("showCalc") &&
      document.getElementById("showCalc").checked
    )
      showCalculationPopup(parseFloat(timeSliderEl.value));
  });
  timeSliderEl.addEventListener("pointerup", () => {
    if (
      document.getElementById("showCalc") &&
      document.getElementById("showCalc").checked
    )
      showCalculationPopup(parseFloat(timeSliderEl.value));
  });
  timeSliderEl.addEventListener("touchend", () => {
    if (
      document.getElementById("showCalc") &&
      document.getElementById("showCalc").checked
    )
      showCalculationPopup(parseFloat(timeSliderEl.value));
  });
}

function loop(timestamp) {
  if (!running) return;
  const deltaTime = (timestamp - lastTimestamp) / 1000;
  lastTimestamp = timestamp;
  const speed = parseFloat(document.getElementById("speedSelect").value);
  currentSimTime += deltaTime * speed;
  if (currentSimTime >= totalFlightTime) {
    currentSimTime = totalFlightTime;
    running = false;
    document.getElementById("start").textContent = "▶";
    showResults(getPreviewSummary());
  }
  document.getElementById("timeSlider").value = currentSimTime;
  drawScene(currentSimTime);
  requestAnimationFrame(loop);
  if (
    document.getElementById("pathTableContainer") &&
    document.getElementById("pathTableContainer").style.display !== "none"
  )
    renderPathTables();
}

function showResults(s) {
  const sel =
    (document.getElementById("previewSelect") || {}).value || "current";
  // do not show launch summary when previewing all paths
  if (sel === "all") return;
  document.getElementById("simulationResultsOverlay").style.display = "flex";
  document.getElementById("resultsContent").innerHTML = `
        <div class="summary-row"><span class="summary-label">Flight Time:</span><span class="summary-val">${s.tFlight.toFixed(2)}s</span></div>
        <div class="summary-row"><span class="summary-label">Max Height:</span><span class="summary-val">${s.yMax.toFixed(2)}m</span></div>
        <div class="summary-row"><span class="summary-label">Range (x):</span><span class="summary-val">${s.xMax.toFixed(2)}m</span></div>
        <div class="summary-row"><span class="summary-label">Peak Time:</span><span class="summary-val">${s.tPeak.toFixed(2)}s</span></div>
        <div class="summary-row"><span class="summary-label">Final |v|:</span><span class="summary-val">${s.v_res.toFixed(1)}m/s</span></div>
    `;
  try {
    positionResultsOverlay();
  } catch (e) {}
  try {
    showCalculationPopup(s);
  } catch (e) {}
}

// Helper to trigger the actual download
function downloadCSV(csvContent, fileName) {
  const blob = new Blob([csvContent], { type: "text/csv" });
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = fileName;
  a.click();
}

document.getElementById("exportPaths").onclick = () => {
  if (savedPaths.length === 0) {
    alert("No paths saved to export.");
    return;
  }

  let csv = "Path,Time(s),x(m),y(m),vx(m/s),vy(m/s),ax(m/s2),ay(m/s2)\n";

  savedPaths.forEach((path, idx) => {
    path.data.forEach((p) => {
      // ax is 0 in standard projectile motion, ay is -g
      csv += `${idx + 1},${p.t.toFixed(2)},${p.x.toFixed(2)},${p.y.toFixed(2)},${p.vx.toFixed(2)},${p.vy.toFixed(2)},0,${(-p.g).toFixed(2)}\n`;
    });
  });

  downloadCSV(csv, "saved_paths_details.csv");
};

// 2. Export Summary Results (Metrics per path)
// Columns: Path Number, Initial Height, Initial Velocity, Angle, Flight Time, Max Height, Peak Time, Range, Final Velocity
document.getElementById("exportSummary").onclick = () => {
  if (savedPaths.length === 0) {
    alert("No paths saved to export. Please save a path first.");
    return;
  }

  let csv =
    "Path Number,Initial Height(m),Initial Velocity(m/s),Angle(deg),Flight Time(s),Max Height(m),Peak Time(s),Range(m),Final Velocity(m/s)\n";

  savedPaths.forEach((path, idx) => {
    // The first data point [0] contains the initial state (t=0)
    // The last data point contains the final state and summary metrics
    const start = path.data[0];
    const end = path.data[path.data.length - 1];

    // Calculate launch angle from components at t=0
    const launchAngle = (Math.atan2(start.vy, start.vx) * 180) / Math.PI;

    // Format the row with the new Initial Height column
    csv +=
      `${idx + 1},` + // Path Number
      `${start.h0.toFixed(2)},` + // Initial Height (y0)
      `${start.v_res.toFixed(2)},` + // Initial Velocity magnitude
      `${launchAngle.toFixed(2)},` + // Angle
      `${end.tFlight.toFixed(2)},` + // Flight Time
      `${end.yMax.toFixed(2)},` + // Max Height
      `${end.tPeak.toFixed(2)},` + // Peak Time
      `${end.xMax.toFixed(2)},` + // Range
      `${end.v_res.toFixed(2)}\n`; // Final Velocity
  });

  downloadCSV(csv, "kinematics_summary_report.csv");
};

/**
 * NEW: manualRefresh now resets the animation state automatically
 * whenever a core physics parameter is changed.
 */
function manualRefresh() {
  // Stop the simulation if it's currently running
  if (running) {
    running = false;
    document.getElementById("start").textContent = "▶";
  }

  // Reset current time to the beginning
  currentSimTime = 0;

  // Recalculate the flight limit for the slider
  const physics = getPhysics(0);
  totalFlightTime = physics.tFlight;

  const slider = document.getElementById("timeSlider");
  if (slider) {
    slider.max = totalFlightTime;
    slider.step = "any";
    slider.value = 0;
    try {
      renderScrubberTicks();
      updateScrubberUI(0);
    } catch (e) {}
  }

  // Reset UI overlays
  document.getElementById("simulationResultsOverlay").style.display = "none";
  try {
    updateHorizontalModeUI();
  } catch (e) {}
  try {
    updateSeparateVectorsToggle(document.getElementById("separateVectors"));
  } catch (e) {}

  // Redraw the scene at T=0
  drawScene(0);
}

function initCharts() {
  charts.forEach((c) => c.destroy());
  charts = [];
  for (let i = 0; i < 3; i++) {
    charts.push(
      new Chart(document.getElementById(`chart${i}`), {
        type: "scatter",
        data: { datasets: [] },
        options: {
          responsive: true,
          maintainAspectRatio: false,
          animation: false,
          plugins: { legend: false },
          scales: { x: { type: "linear", min: 0 } },
        },
      }),
    );
  }
}
function changeGraph(idx, val) {
  chartTypes[idx] = val;
  drawScene(currentSimTime);
}
window.onresize = () => {
  const rect = document.getElementById("animationPane").getBoundingClientRect();
  W = rect.width;
  H = rect.height - 60;
  canvas.width = W;
  canvas.height = H;
  drawScene(currentSimTime);
};
let suppressOverlayPositioning = false;
window.addEventListener("resize", () => {
  try {
    if (!suppressOverlayPositioning) positionResultsOverlay();
  } catch (e) {}
});
window.addEventListener("resize", () => {
  try {
    if (!suppressOverlayPositioning) positionEquationGraph();
  } catch (e) {}
});
let animWidthLocked = false;
let lockedAnimWidth = 0;

// Freeze overlays (instant details, track ball, results) by switching them to fixed pixel positions
function freezeOverlaysDuringDrag() {
  const ids = ["instantDetails", "trackBallPane", "simulationResultsOverlay"];
  ids.forEach((id) => {
    try {
      const el = document.getElementById(id);
      if (!el) return;
      const rect = el.getBoundingClientRect();
      // store previous positioning values so we can restore
      el.__prevPos = {
        position: el.style.position || "",
        left: el.style.left || "",
        top: el.style.top || "",
        right: el.style.right || "",
        transform: el.style.transform || "",
        transition: el.style.transition || "",
      };
      el.style.position = "fixed";
      el.style.left = rect.left + "px";
      el.style.top = rect.top + "px";
      el.style.right = "auto";
      el.style.transform = "none";
      el.style.transition = "none";
    } catch (e) {}
  });
}

function restoreOverlaysAfterDrag() {
  const ids = ["instantDetails", "trackBallPane", "simulationResultsOverlay"];
  ids.forEach((id) => {
    try {
      const el = document.getElementById(id);
      if (!el) return;
      const prev = el.__prevPos || null;
      if (prev) {
        el.style.position = prev.position;
        el.style.left = prev.left;
        el.style.top = prev.top;
        el.style.right = prev.right;
        el.style.transform = prev.transform;
        el.style.transition = prev.transition;
        delete el.__prevPos;
      }
    } catch (e) {}
  });
}
// splitter drag logic
const splitter = document.getElementById("splitter");
let isDraggingSplitter = false;
let startDragY = 0;
let startTopHeight = 0;
function updateSplitterVisibility() {
  const graphsCheckbox = document.getElementById("showGraphs");
  if (!splitter) return;
  if (graphsCheckbox && graphsCheckbox.checked) {
    splitter.style.display = "block";
  } else {
    splitter.style.display = "none";
    // reset flex sizing so layout returns to default
    const anim = document.getElementById("animationPane");
    const graph = document.getElementById("graphContainer");
    if (anim) {
      anim.style.flex = "";
      anim.style.height = "";
    }
    if (graph) {
      graph.style.flex = "";
      graph.style.height = "";
    }
  }
}

if (splitter) {
  splitter.addEventListener("mousedown", (e) => {
    isDraggingSplitter = true;
    startDragY = e.clientY;
    const animRect = document
      .getElementById("animationPane")
      .getBoundingClientRect();
    startTopHeight = animRect.height;
    // suppress repositioning of overlays while user is actively dragging
    suppressOverlayPositioning = true;
    // freeze overlays in place so they don't slide while resizing
    try {
      freezeOverlaysDuringDrag();
    } catch (e) {}
    // lock animation pane width in pixels so it doesn't flex-shrink during vertical drag
    try {
      const anim = document.getElementById("animationPane");
      if (anim) {
        lockedAnimWidth = anim.getBoundingClientRect().width;
        anim.style.minWidth = lockedAnimWidth + "px";
        anim.style.maxWidth = lockedAnimWidth + "px";
        anim.style.width = lockedAnimWidth + "px";
        animWidthLocked = true;
      }
    } catch (e) {}
    document.body.style.userSelect = "none";
  });
  window.addEventListener("mousemove", (e) => {
    if (!isDraggingSplitter) return;
    const main = document.getElementById("mainArea");
    if (!main) return;
    const rect = main.getBoundingClientRect();
    let newTop = startTopHeight + (e.clientY - startDragY);
    const minTop = 120;
    const minBottom = 120; // px
    newTop = Math.max(minTop, Math.min(rect.height - minBottom, newTop));
    const bottomH = rect.height - newTop - (splitter.offsetHeight || 8);
    const anim = document.getElementById("animationPane");
    const graph = document.getElementById("graphContainer");
    if (anim && graph) {
      anim.style.flex = "0 0 " + newTop + "px";
      anim.style.height = newTop + "px";
      graph.style.flex = "0 0 " + bottomH + "px";
      graph.style.height = bottomH + "px";
      // trigger resize and redraw so canvas and charts update immediately
      try {
        window.dispatchEvent(new Event("resize"));
        if (Array.isArray(charts))
          charts.forEach((c) => c && c.resize && c.resize());
      } catch (e) {}
      try {
        drawScene(currentSimTime);
      } catch (e) {}
    }
  });
  window.addEventListener("mouseup", () => {
    if (isDraggingSplitter) {
      isDraggingSplitter = false;
      document.body.style.userSelect = "";
      // re-enable overlay positioning and force a single reposition + redraw at drag end
      suppressOverlayPositioning = false;
      try {
        restoreOverlaysAfterDrag();
      } catch (e) {}
      try {
        positionResultsOverlay();
      } catch (e) {}
      try {
        if (Array.isArray(charts))
          charts.forEach((c) => c && c.resize && c.resize());
      } catch (e) {}
      try {
        drawScene(currentSimTime);
      } catch (e) {}
      // restore animation pane width responsiveness
      try {
        const anim = document.getElementById("animationPane");
        if (anim && animWidthLocked) {
          anim.style.minWidth = "";
          anim.style.maxWidth = "";
          anim.style.width = "";
          animWidthLocked = false;
        }
      } catch (e) {}
    }
  });
  // touch support
  splitter.addEventListener(
    "touchstart",
    (e) => {
      if (e.touches && e.touches[0]) {
        isDraggingSplitter = true;
        startDragY = e.touches[0].clientY;
        const animRect = document
          .getElementById("animationPane")
          .getBoundingClientRect();
        startTopHeight = animRect.height; // suppress overlay moves during touch-drag
        suppressOverlayPositioning = true;
        try {
          freezeOverlaysDuringDrag();
        } catch (e) {}
        document.body.style.userSelect = "none";
      }
    },
    { passive: false },
  );
  window.addEventListener(
    "touchmove",
    (e) => {
      if (!isDraggingSplitter || !e.touches || !e.touches[0]) return;
      const main = document.getElementById("mainArea");
      const rect = main.getBoundingClientRect();
      let newTop = startTopHeight + (e.touches[0].clientY - startDragY);
      const minTop = 120;
      const minBottom = 120;
      newTop = Math.max(minTop, Math.min(rect.height - minBottom, newTop));
      const bottomH = rect.height - newTop - (splitter.offsetHeight || 8);
      const anim = document.getElementById("animationPane");
      const graph = document.getElementById("graphContainer");
      if (anim && graph) {
        anim.style.flex = "0 0 " + newTop + "px";
        anim.style.height = newTop + "px";
        graph.style.flex = "0 0 " + bottomH + "px";
        graph.style.height = bottomH + "px";
        try {
          window.dispatchEvent(new Event("resize"));
          if (Array.isArray(charts))
            charts.forEach((c) => c && c.resize && c.resize());
        } catch (e) {}
        try {
          drawScene(currentSimTime);
        } catch (e) {}
      }
      e.preventDefault();
    },
    { passive: false },
  );
  window.addEventListener("touchend", () => {
    if (isDraggingSplitter) {
      isDraggingSplitter = false;
      document.body.style.userSelect = "";
      suppressOverlayPositioning = false;
      try {
        restoreOverlaysAfterDrag();
      } catch (e) {}
      try {
        positionResultsOverlay();
      } catch (e) {}
      try {
        if (Array.isArray(charts))
          charts.forEach((c) => c && c.resize && c.resize());
      } catch (e) {}
      try {
        drawScene(currentSimTime);
      } catch (e) {} // restore width lock
      try {
        const anim = document.getElementById("animationPane");
        if (anim && animWidthLocked) {
          anim.style.minWidth = "";
          anim.style.maxWidth = "";
          anim.style.width = "";
          animWidthLocked = false;
        }
      } catch (e) {}
    }
  });
}

// call once to initialize
setTimeout(updateSplitterVisibility, 150);

populateDropdowns();
initCharts();
setTimeout(window.onresize, 100);
try {
  renderScrubberTicks();
  updateScrubberUI(0);
} catch (e) {}
// initialize kinematic equation buttons (no default selection)
try {
  applyKinematicSelection();
} catch (e) {}
try {
  positionEquationGraph();
} catch (e) {}
// initialize visibility state of the Path Data option based on Graphs checkbox
try {
  updatePathDataOptionVisibility();
} catch (e) {}
// Ensure separate-vectors control reflects current initial state on first open
try {
  updateSeparateVectorsToggle(document.getElementById("separateVectors"));
} catch (e) {}
// initialize savedShowPathData to the current checkbox state and keep it in sync
{
  const pcb = document.getElementById("showPathData");
  if (pcb) {
    savedShowPathData = !!pcb.checked;
    pcb.addEventListener("change", (e) => {
      savedShowPathData = !!e.target.checked;
    });
  }
}
// initialize savedTrackBallState to the current checkbox state and keep it in sync
{
  const tcb = document.getElementById("showTrackBall");
  if (tcb) {
    savedTrackBallState = !!tcb.checked;
    tcb.addEventListener("change", (e) => {
      savedTrackBallState = !!e.target.checked;
    });
  }
}

function renderKinematicEquationButtons(attempts) {
  attempts = attempts || 0;
  if (typeof katex === "undefined") {
    if (attempts < 10)
      return setTimeout(
        () => renderKinematicEquationButtons(attempts + 1),
        120,
      );
    return; // give up after several tries
  }
  document.querySelectorAll(".katexEq").forEach((el) => {
    const latex = el.dataset.latex || "";
    try {
      katex.render(latex, el, {
        throwOnError: false,
        trust: true,
        displayMode: false,
      });
    } catch (e) {
      el.textContent = latex;
    }
  });
}
// render now and again on DOMContentLoaded (polling in case KaTeX loads slightly later)
try {
  renderKinematicEquationButtons();
} catch (e) {}
document.addEventListener("DOMContentLoaded", () => {
  try {
    renderKinematicEquationButtons();
  } catch (e) {}
});
// also ensure buttons render after full load
window.addEventListener("load", () => {
  try {
    renderKinematicEquationButtons();
  } catch (e) {}
});
