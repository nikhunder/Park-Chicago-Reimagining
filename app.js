// Street Direction, read-only public viewer. Plain Leaflet.js, no
// framework - the interactive editor (../python/app.py) is Dash/React for
// its click-heavy multi-session editing workflow, but this page only ever
// needs to draw layers and step an index, so a hand-written render loop
// here carries none of that earlier project's hand-rolled-JS risk (no
// bearing/rotation math is done in this file - every chevron coordinate
// is precomputed server-side by build_static_data.py and shipped as plain
// coordinates to draw).

const COLORS = { reversal: "#111111", contraflow: "#2f8f6a" };

const renderer = L.canvas({ padding: 0.5 });

const map = L.map("map", {
  center: DATA.meta.center,
  zoom: 11,
  preferCanvas: true,
});

// Explicit panes, low to high z-index, so stacking order is fixed
// regardless of draw order: context lines, then road-name labels, then
// the highlighted change + ward boundary, then control-point markers on
// top of everything.
map.createPane("linesPane").style.zIndex = 400;
map.createPane("labelsPane").style.zIndex = 405;
map.createPane("highlightPane").style.zIndex = 407;
map.createPane("controlPane").style.zIndex = 410;
map.getPane("labelsPane").style.pointerEvents = "none";

L.tileLayer("https://{s}.basemaps.cartocdn.com/light_nolabels/{z}/{x}/{y}{r}.png?key=cb1_2y7m_1_548aa4aac63350462978d1a1", {
  attribution: "&copy; OpenStreetMap contributors &copy; CARTO",
  pane: "tilePane",
}).addTo(map);

L.tileLayer("https://{s}.basemaps.cartocdn.com/light_only_labels/{z}/{x}/{y}{r}.png?key=cb1_2y7m_1_548aa4aac63350462978d1a1", {
  pane: "labelsPane",
}).addTo(map);

// --- Context layers (drawn once, never change) -----------------------
//
// Grouped into `contextLayer` and hidden below CONTEXT_MIN_ZOOM: at a
// citywide/ward overview zoom, thousands of chevrons and control-point
// dots visually bury the sparse highlighted changes, which defeats the
// point of "Show all changes." Hidden until the user is one zoom level
// short of the per-change view (maxZoom 16 in render()), so zooming in
// on a cluster brings full context back exactly where they land.
const CONTEXT_MIN_ZOOM = 15;
const contextLayer = L.layerGroup();

function drawNamedLines(entries, color, weight, opacity) {
  const group = L.layerGroup();
  for (const e of entries) {
    const opts = { color, weight, opacity, interactive: !!e.name, renderer, pane: "linesPane" };
    const pl = L.polyline(e.line, opts);
    if (e.name) pl.bindTooltip(e.name);
    pl.addTo(group);
  }
  group.addTo(contextLayer);
  return group;
}

// Parks (light fill, always visible - low visual weight, useful for
// orientation even at a citywide zoom).
for (const ring of DATA.parks) {
  L.polygon(ring, { color: "#2f8f4a", weight: 1, fillOpacity: 0.25, fillColor: "#2f8f4a",
                     interactive: false, renderer, pane: "linesPane" }).addTo(map);
}

// Minor arterial (class 3), then arterial (class 1-2) on top of it
drawNamedLines(DATA.boundingCol, "#b8842a", 2, 0.85);
drawNamedLines(DATA.boundingArt, "#b5453d", 3, 0.85);

// Current one-way direction chevrons, every one-way street citywide
for (const chevron of DATA.baseArrows) {
  L.polyline(chevron, { color: "#7a8a99", weight: 2, opacity: 0.9,
                         interactive: false, renderer, pane: "linesPane" }).addTo(contextLayer);
}

// Control points, drawn above the road-name labels. Stop signs and traffic
// signals get their own toggleable layers (see the layer-toggle registry
// below) rather than living in contextLayer, since the sidebar checkboxes
// let a viewer hide them independently of zoom.
function drawPoints(entries, radius, color, fillOpacity) {
  const group = L.layerGroup();
  for (const [lat, lon] of entries) {
    L.circleMarker([lat, lon], { radius, color, weight: 1.5, fillOpacity,
                                  interactive: false, renderer, pane: "controlPane" }).addTo(group);
  }
  return group;
}
const stopSignLayer = L.layerGroup();
drawPoints(DATA.stopOther, 4, "#d4913d", 0).addTo(stopSignLayer);
drawPoints(DATA.stopAll, 2.5, "#d4913d", 1).addTo(stopSignLayer);
const signalLayer = L.layerGroup();
drawPoints(DATA.signals, 5, "#3d8bd4", 1).addTo(signalLayer);

function updateContextVisibility() {
  const shouldShow = map.getZoom() >= CONTEXT_MIN_ZOOM;
  const isShown = map.hasLayer(contextLayer);
  if (shouldShow && !isShown) contextLayer.addTo(map);
  else if (!shouldShow && isShown) map.removeLayer(contextLayer);
}
map.on("zoomend", updateContextVisibility);
updateContextVisibility();

// --- Ward selector ------------------------------------------------------

const wardSelect = document.getElementById("ward-select");
for (const num of Object.keys(DATA.wards).map(Number).sort((a, b) => a - b)) {
  const opt = document.createElement("option");
  opt.value = num;
  opt.textContent = `Ward ${num}`;
  wardSelect.appendChild(opt);
}

function activeBounds() {
  return wardSelect.value ? DATA.wards[Number(wardSelect.value)].bounds : DATA.meta.bounds;
}

// Ward boundaries + number labels - hidden until zoomed in at least as
// far as the "Focus ward" dropdown itself would zoom to. Checked every
// individual ward's own fit-to-bounds zoom (map.getBoundsZoom) and they
// cluster tightly at 13-15 (mostly 14) since Chicago's wards are all
// similar in area by design - a fixed threshold, not one computed from
// whatever bounds the map just flew to (that was tried first and was a
// no-op, since flyToBounds always lands AT its own fit zoom, making
// "zoom >= the zoom this exact flight targeted" always true).
const WARD_MIN_ZOOM = 14;
const wardBoundaryLayer = L.layerGroup();
for (const [num, w] of Object.entries(DATA.wards)) {
  for (const ring of w.boundary) {
    L.polygon(ring, { color: "#8a5fbf", weight: 2, opacity: 0.7, fillOpacity: 0,
                       dashArray: "6,4", interactive: false, renderer, pane: "highlightPane" })
      .addTo(wardBoundaryLayer);
  }
  L.marker(w.label, {
    icon: L.divIcon({ className: "ward-label", html: `Ward ${num}`, iconSize: [60, 16] }),
    interactive: false, pane: "highlightPane",
  }).addTo(wardBoundaryLayer);
}

// --- Existing CDOT bike facilities --------------------------------------
//
// Shown at the same zoom threshold as ward boundaries (rather than buried
// in contextLayer behind CONTEXT_MIN_ZOOM) since they're a primary
// reference layer, not incidental clutter. Styled by facility type - line
// pattern carries the type so it reads in print/grayscale too, color alone
// isn't overloaded with meaning, and a blue distinct from both the black
// reversal and green contraflow proposal colors avoids implying a proposed
// change.
const BIKE_COLOR = "#1a6faa";
const BIKE_STYLE = {
  protected: { dashArray: null, weight: 4 },
  buffered: { dashArray: "10,5", weight: 3.5 },
  lane: { dashArray: "4,4", weight: 2.5 },
  shared: { dashArray: "1,6", weight: 2.5 },
  greenway: { dashArray: "14,4,2,4", weight: 3 },
};
const bikeLayer = L.layerGroup();
for (const route of DATA.bikeRoutes) {
  const style = BIKE_STYLE[route.type] || BIKE_STYLE.lane;
  L.polyline(route.line, { color: BIKE_COLOR, weight: style.weight, opacity: 0.8,
                            dashArray: style.dashArray, interactive: false,
                            renderer, pane: "linesPane" }).addTo(bikeLayer);
}

// --- Layer toggles -------------------------------------------------------
//
// Each of these four layers is still hidden below its own zoom threshold
// (thousands of stop-sign/signal dots at a citywide zoom are as unreadable
// as the chevrons contextLayer already guards against), but the sidebar
// checkboxes let a viewer additionally turn any of them off outright -
// the two conditions are ANDed together in updateLayerVisibility.
const LAYER_TOGGLES = {
  wards: { layer: wardBoundaryLayer, minZoom: WARD_MIN_ZOOM, enabled: true },
  bike: { layer: bikeLayer, minZoom: WARD_MIN_ZOOM, enabled: true },
  stops: { layer: stopSignLayer, minZoom: CONTEXT_MIN_ZOOM, enabled: true },
  signals: { layer: signalLayer, minZoom: CONTEXT_MIN_ZOOM, enabled: true },
};

function updateLayerVisibility() {
  const zoom = map.getZoom();
  for (const key in LAYER_TOGGLES) {
    const entry = LAYER_TOGGLES[key];
    const shouldShow = entry.enabled && zoom >= entry.minZoom;
    const isShown = map.hasLayer(entry.layer);
    if (shouldShow && !isShown) entry.layer.addTo(map);
    else if (!shouldShow && isShown) map.removeLayer(entry.layer);
  }
}
map.on("zoomend", updateLayerVisibility);
updateLayerVisibility();

document.getElementById("toggle-wards").addEventListener("change", (e) => {
  LAYER_TOGGLES.wards.enabled = e.target.checked;
  updateLayerVisibility();
});
document.getElementById("toggle-bike").addEventListener("change", (e) => {
  LAYER_TOGGLES.bike.enabled = e.target.checked;
  updateLayerVisibility();
});
document.getElementById("toggle-stops").addEventListener("change", (e) => {
  LAYER_TOGGLES.stops.enabled = e.target.checked;
  updateLayerVisibility();
});
document.getElementById("toggle-signals").addEventListener("change", (e) => {
  LAYER_TOGGLES.signals.enabled = e.target.checked;
  updateLayerVisibility();
});

// --- The highlighted change (current selection) --------------------------

let highlightLayer = L.layerGroup().addTo(map);

function drawHighlight(change) {
  highlightLayer.clearLayers();
  const color = COLORS[change.action];
  L.polyline(change.line, { color, weight: 5, opacity: 1, interactive: false,
                             pane: "highlightPane" }).addTo(highlightLayer);
  L.polyline(change.proposedChevron, { color, weight: 3, opacity: 1, interactive: false,
                                        pane: "highlightPane" }).addTo(highlightLayer);
}

// --- Navigation: step through changes one at a time, or see them all -----

let activeChanges = DATA.changes;
let currentIndex = 0;
let overviewMode = false;

function actionLabel(action) {
  return action === "contraflow" ? "Contraflow bike lane" : "Reversal";
}

function renderOverview() {
  const counter = document.getElementById("nav-counter");
  const info = document.getElementById("change-info");
  const prevBtn = document.getElementById("prev-btn");
  const nextBtn = document.getElementById("next-btn");
  const showAllBtn = document.getElementById("show-all-btn");

  highlightLayer.clearLayers();
  activeChanges.forEach((c, i) => {
    const color = COLORS[c.action];
    const line = L.polyline(c.line, { color, weight: 3, opacity: 0.9,
                                       interactive: true, renderer, pane: "highlightPane" });
    line.on("click", () => {
      overviewMode = false;
      currentIndex = i;
      render();
    });
    line.addTo(highlightLayer);
    L.polyline(c.proposedChevron, { color, weight: 2, opacity: 1, interactive: false,
                                     pane: "highlightPane" }).addTo(highlightLayer);
  });

  const scope = wardSelect.value ? `in Ward ${wardSelect.value}` : "citywide";
  counter.textContent = `Showing all ${activeChanges.length} changes ${scope}`;
  showAllBtn.classList.add("active");
  showAllBtn.textContent = "Showing all changes, click to browse one at a time";

  const nRev = activeChanges.filter((c) => c.action === "reversal").length;
  const nCon = activeChanges.filter((c) => c.action === "contraflow").length;
  info.innerHTML = "";
  const summary = document.createElement("div");
  summary.className = "detail-row";
  summary.textContent = `${nRev} reversal${nRev === 1 ? "" : "s"}, `
    + `${nCon} contraflow bike lane${nCon === 1 ? "" : "s"}.`;
  info.appendChild(summary);

  prevBtn.disabled = activeChanges.length === 0;
  nextBtn.disabled = activeChanges.length === 0;
  map.flyToBounds(activeBounds(), { duration: 0.4 });
}

function render() {
  const showAllBtn = document.getElementById("show-all-btn");
  showAllBtn.classList.remove("active");
  showAllBtn.textContent = "Show all changes";
  if (overviewMode) {
    renderOverview();
    return;
  }

  const counter = document.getElementById("nav-counter");
  const info = document.getElementById("change-info");
  const prevBtn = document.getElementById("prev-btn");
  const nextBtn = document.getElementById("next-btn");

  if (activeChanges.length === 0) {
    counter.textContent = "No proposed changes in this ward.";
    info.textContent = "";
    prevBtn.disabled = true;
    nextBtn.disabled = true;
    highlightLayer.clearLayers();
    return;
  }
  prevBtn.disabled = false;
  nextBtn.disabled = false;

  const change = activeChanges[currentIndex];
  const scope = wardSelect.value ? `in Ward ${wardSelect.value}` : "citywide";
  counter.textContent = `Change ${currentIndex + 1} of ${activeChanges.length} ${scope}`;

  const crossParts = [];
  if (change.crossStart) crossParts.push(change.crossStart);
  if (change.crossEnd && change.crossEnd !== change.crossStart) crossParts.push(change.crossEnd);
  const crossText = crossParts.length ? `Between ${crossParts.join(" and ")}` : "";

  info.innerHTML = "";
  const streetEl = document.createElement("span");
  streetEl.className = "street";
  streetEl.textContent = change.street;
  const badgeEl = document.createElement("span");
  badgeEl.className = `action-badge ${change.action}`;
  badgeEl.textContent = actionLabel(change.action);
  info.appendChild(streetEl);
  info.appendChild(badgeEl);
  if (change.segments > 1) {
    const blocksEl = document.createElement("span");
    blocksEl.className = "blocks-note";
    blocksEl.textContent = `${change.segments} connected blocks`;
    info.appendChild(blocksEl);
  }
  if (crossText) {
    const row = document.createElement("div");
    row.className = "detail-row";
    row.textContent = crossText;
    info.appendChild(row);
  }
  const wardRow = document.createElement("div");
  wardRow.className = "detail-row";
  wardRow.innerHTML = `<b>Ward:</b> ${change.ward !== null ? change.ward : "unknown"}`;
  info.appendChild(wardRow);

  const cellRow = document.createElement("div");
  cellRow.className = "detail-row debug";
  cellRow.innerHTML = `<b>Cell:</b> ${change.cellId !== null ? change.cellId : "unknown"}`;
  info.appendChild(cellRow);

  drawHighlight(change);
  map.flyToBounds(change.bounds, { padding: [60, 60], maxZoom: 16, duration: 0.4 });
}

function step(direction) {
  if (activeChanges.length === 0) return;
  overviewMode = false;
  currentIndex = (currentIndex + direction + activeChanges.length) % activeChanges.length;
  render();
}

document.getElementById("prev-btn").addEventListener("click", () => step(-1));
document.getElementById("next-btn").addEventListener("click", () => step(1));
document.getElementById("show-all-btn").addEventListener("click", () => {
  overviewMode = true;
  render();
});

document.addEventListener("keydown", (e) => {
  if (e.key === "ArrowRight") step(1);
  else if (e.key === "ArrowLeft") step(-1);
});

wardSelect.addEventListener("change", () => {
  const val = wardSelect.value;
  activeChanges = val === "" ? DATA.changes : DATA.changes.filter((c) => c.ward === Number(val));
  currentIndex = 0;
  updateLayerVisibility();
  render();
});

render();
document.getElementById("loading").style.display = "none";
