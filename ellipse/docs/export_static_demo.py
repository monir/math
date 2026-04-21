#!/usr/bin/env python3
"""
export_static_demo.py — Generate a fully static index.html from the demo
=========================================================================
Runs all precomputation, bakes data into HTML, adds JS formula implementations
so the page works without any server. Just open index.html in a browser.

Usage:
    python3 export_static_demo.py [--output path/to/index.html]

Precision: All pre-computed sweep data uses mpmath (50 digits). Live computation
uses JS float64 AGM for E(m) — 15+ significant digits, 6 orders of magnitude
more than needed for ppb-level error display.
"""
import sys
import os
import json

_demo_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _demo_dir)
sys.path.insert(0, os.path.join(_demo_dir, '..', 'src'))

print("Importing demo module (triggers precomputation, ~2 min)...")
import ellipse_web_demo as demo
from formulas import _TOWER

# =========================================================================
# JS formula implementations
# =========================================================================

# Collect tower layer data for JS embedding
tower_layers_js = json.dumps([
    {'N': layer['N'], 'D': layer['D'], 'onset': layer['onset']}
    for layer in _TOWER
])

JS_FORMULAS = r"""
// =========================================================================
// LOCAL COMPUTATION — replaces /api/compute server endpoint
// All formulas implemented in JS float64 (15+ sig digits)
// =========================================================================

// --- Complete Elliptic Integral E(m) via AGM ---
function ellipticE(m) {
    // Complete elliptic integral E(m) via AGM with c-value accumulation.
    // Machine-precision (errors at 2.2e-16) verified against mpmath.
    if (m <= 0) return Math.PI / 2;
    if (m >= 1) return 1;
    var a = 1, b = Math.sqrt(1 - m);
    var S = m / 2;  // n=0 term: 2^{-1} * c_0^2, where c_0 = sqrt(m)
    var factor = 1; // 2^{n-1} for n=1 -> 2^0 = 1
    for (var n = 0; n < 30; n++) {
        var c = (a - b) / 2;
        S += factor * c * c;
        var a1 = (a + b) / 2;
        var b1 = Math.sqrt(a * b);
        a = a1; b = b1;
        factor *= 2;
        if (Math.abs(c) < 1e-16 * Math.abs(a)) break;
    }
    return (Math.PI / (2 * a)) * (1 - S);
}

function exactPerimeter(a, b) {
    if (a < b) { var t = a; a = b; b = t; }
    if (a <= 0) return 0;
    if (a === b) return 2 * Math.PI * a;
    var e2 = 1 - (b / a) * (b / a);
    return 4 * a * ellipticE(e2);
}

// --- Shared helpers ---
function hParam(a, b) {
    if (a < b) { var t = a; a = b; b = t; }
    var d = (a - b) / (a + b);
    return d * d;
}

function ramanujanII(a, b) {
    if (a < b) { var t = a; a = b; b = t; }
    var h = hParam(a, b);
    return Math.PI * (a + b) * (1 + 3 * h / (10 + Math.sqrt(4 - 3 * h)));
}

// --- Tower layers (pre-computed from Pade construction) ---
var TOWER_LAYERS = """ + tower_layers_js + r""";

function towerBaseRatio(h, level) {
    if (h <= 0) return 1;
    var R = 1 + 3 * h / (10 + Math.sqrt(4 - 3 * h));
    for (var i = 0; i < Math.min(level, TOWER_LAYERS.length); i++) {
        var L = TOWER_LAYERS[i];
        var N = L.N, D = L.D, onset = L.onset;
        var Nv = N[0] + h * (N[1] + h * (N[2] + h * N[3]));
        var Dv = D[0] + h * (D[1] + h * D[2]);
        if (Math.abs(Dv) > 1e-30) {
            R += Math.pow(h, onset) * Nv / Dv;
        }
    }
    return R;
}

function towerPerimeter(a, b, level) {
    if (a < b) { var t = a; a = b; b = t; }
    var h = hParam(a, b);
    return Math.PI * (a + b) * towerBaseRatio(h, level);
}

function towerCorrected(a, b, level, rates, coeffs, lam, qGate) {
    if (a < b) { var t = a; a = b; b = t; }
    var h = hParam(a, b);
    var x = 1 - h;
    var Prk = towerPerimeter(a, b, level);
    var phi = 0;
    for (var i = 0; i < rates.length; i++) {
        phi += coeffs[i] * Math.exp(-rates[i] * lam * x);
    }
    var gate = Math.pow(h, qGate);
    var denom = 1 - gate * phi;
    if (denom <= 0 || !isFinite(denom)) return NaN;
    return Prk / denom;
}

function towerCorrectedSCOR(a, b, level, rates, expCoeffs, logCoeffs, lam, qGate) {
    if (a < b) { var t = a; a = b; b = t; }
    var h = hParam(a, b);
    var x = 1 - h;
    var Prk = towerPerimeter(a, b, level);
    var phi = 0;
    for (var i = 0; i < rates.length; i++) {
        phi += expCoeffs[i] * Math.exp(-rates[i] * lam * x);
    }
    // Logarithmic enrichment: d_k * x^k * ln(x) for k=1,2,3
    if (x > 0) {
        var lnx = Math.log(x);
        var xk = x;
        for (var j = 0; j < logCoeffs.length; j++) {
            phi += logCoeffs[j] * xk * lnx;
            xk *= x;
        }
    }
    var gate = Math.pow(h, qGate);
    var denom = 1 - gate * phi;
    if (denom <= 0 || !isFinite(denom)) return NaN;
    return Prk / denom;
}

// --- All 11 methods ---
var METHODS_JS = [
    {name: "Ramanujan I (1914)", fn: function(a, b) {
        if (a < b) { var t = a; a = b; b = t; }
        return Math.PI * (3 * (a + b) - Math.sqrt((3 * a + b) * (a + 3 * b)));
    }, isOurs: false},
    {name: "Ramanujan II (1914)", fn: ramanujanII, isOurs: false},
    {name: "Cantrell (2001)", fn: function(a, b) {
        if (a < b) { var t = a; a = b; b = t; }
        var h = hParam(a, b);
        var c = 4 / Math.PI - 14 / 11;
        return Math.PI * (a + b) * (1 + 3 * h / (10 + Math.sqrt(4 - 3 * h) + c * Math.pow(h, 1.5)));
    }, isOurs: false},
    {name: "Ayala-Rendón R2/2exp (2025)", fn: function(a, b) {
        if (a < b) { var t = a; a = b; b = t; }
        var h = hParam(a, b);
        var x = 1 - h;
        var term = 3.37528e-4 * Math.exp(-10.29662 * x) + 6.48093e-5 * Math.exp(-40.89043 * x);
        return ramanujanII(a, b) / (1 - term);
    }, isOurs: false},
    {name: "Mamoun R2/2exp (0.530 ppm)", fn: function(a, b) {
        if (a < b) { var t = a; a = b; b = t; }
        var h = hParam(a, b);
        var x = 1 - h;
        var phi = 6.5882e-5 * Math.exp(-40.1273 * x) + 3.3646e-4 * Math.exp(-10.2653 * x);
        return ramanujanII(a, b) * (1 + Math.pow(h, 0.01) * phi);
    }, isOurs: true},
    {name: "Mamoun R2/3exp (0.083 ppm)", fn: function(a, b) {
        if (a < b) { var t = a; a = b; b = t; }
        var h = hParam(a, b);
        var x = 1 - h;
        var T_FLAT = 1 - 7 * Math.PI / 22;
        var R_v = 0.3725797305793, S_v = 0.0360560365885;
        var A_v = T_FLAT / (1 + R_v + S_v);
        var B_v = R_v * A_v, C_v = S_v * A_v;
        var lam = 6.8954698854899;
        var term = A_v * Math.exp(-lam * x) + B_v * Math.exp(-3.24 * lam * x) + C_v * Math.exp(-15 * lam * x);
        var denom = 1 - Math.pow(h, 7/3) * term;
        if (denom <= 0 || !isFinite(denom)) return NaN;
        return ramanujanII(a, b) / denom;
    }, isOurs: true},
    {name: "Mamoun R3+15exp (1.427 ppb)", fn: function(a, b) {
        return towerCorrected(a, b, 1,
            [3/7, 2/3, 1, 7/6, 3/2, 53/25, 81/25, 162/25, 189/25, 13, 15, 292/15, 24, 30, 35],
            [1.0690331487437538e-06, -5.3446219367020315e-06, -4.0279727459249e-06,
             -5.069600273319092e-06, -5.344344263799115e-06, 3.8078085513734217e-06,
             9.539748048443633e-06, -3.4773795578775624e-06, 1.0344348076505942e-05,
             -3.937426561235638e-06, -3.3525450185435064e-06, 1.0593006595991767e-05,
             -3.0640908934958932e-06, -5.328578613384776e-06, 3.677529114762622e-06],
            14.563322134576083, 3.416383861577742);
    }, isOurs: true},
    {name: "Mamoun R4+20exp (0.492 ppb)", fn: function(a, b) {
        return towerCorrected(a, b, 2,
            [1/3, 3/7, 3/4, 1, 7/6, 7/3, 3, 81/25, 292/63, 5, 189/25, 9, 12, 15, 17, 25, 30, 35, 45, 70],
            [-1.5937722286313696e-06, 4.004676507772733e-06, -6.07781259758309e-06,
             -1.7887837164351737e-05, 7.004699361980741e-06, -1.534340458195682e-06,
             8.604354677488707e-06, -5.918840736648467e-07, 4.016298270455695e-06,
             2.308529236939859e-06, -4.070618365020088e-06, 6.387425123480058e-06,
             -4.4507260538806865e-07, -7.202231753854354e-06, 9.243836492981317e-06,
             -3.985839132116884e-06, -1.6398228803520656e-06, 5.453076591436378e-06,
             -2.3199601822721373e-06, 3.261112304827786e-07],
            15.802299362305348, 2.519930815428779);
    }, isOurs: true},
    {name: "Mamoun R5+16exp (0.045 ppb)", fn: function(a, b) {
        return towerCorrected(a, b, 3,
            [0.29878611440337327, 0.3572365501509249, 0.41828921662677127,
             0.5677005934267171, 0.770726605612723, 0.9495851373843635,
             1.1698946276558106, 2.3239087718175355, 4.205557610686093,
             8.283583529370196, 15.27658749199377, 18.649332712735315,
             27.835229882813813, 35.73422684428793, 113.10794979750942,
             135.17573511621515],
            [-2.588676620699167e-04, 1.220803421717380e-03, -1.651798604942254e-03,
             1.262847441025102e-03, -1.136064899841650e-03, 7.192927096587283e-04,
             -1.714984099958837e-04, 1.161648316508942e-05, 2.048063475485459e-06,
             1.551829455810800e-06, -1.263090356927472e-06, 1.733089858132272e-06,
             -8.106411423336153e-07, 4.107631652705958e-07, -3.194250873988154e-08,
             3.155489726726257e-08],
            23.688420305684442, 7.890699853691736);
    }, isOurs: true},
    {name: "Mamoun R6+16exp (0.018 ppb)", fn: function(a, b) {
        return towerCorrected(a, b, 4,
            [0.0549124247701398, 0.08959272582690402, 0.24697733467232463,
             0.34396214628787214, 0.4655283978174422, 0.7113920398223701,
             0.7744047899716632, 0.9210079249587176, 3.6495347918051557,
             10.887815967669043, 15.97715116830682, 20.6025317043627,
             30.355128560816556, 37.275181367113625, 124.98285889270504,
             134.9403146022634],
            [-7.359744999391803e-05, 1.706784926004658e-04, -9.198418581482057e-04,
             2.098920312370626e-03, -2.202085191328198e-03, 4.629004663174692e-03,
             -4.457178135606173e-03, 7.500881981855032e-04, 3.301248630070683e-06,
             1.072154845813948e-06, -1.256312076107994e-06, 1.211037623371705e-06,
             -6.351727102404296e-07, 3.184720885884841e-07, -3.842030381483090e-08,
             3.792170023733917e-08],
            31.352571607846436, 11.817567226046656);
    }, isOurs: true},
    {name: "Mamoun R6+16exp+3log SCOR (0.007 ppb)", fn: function(a, b) {
        return towerCorrectedSCOR(a, b, 4,
            [0.010166999187513546, 0.07776780092888144, 0.19901003723401806,
             0.338043080886615, 0.4971009768543303, 0.7070725423114185,
             0.8722016136238608, 2.7314795971348453, 4.740243707070392,
             9.970442852904373, 14.936436441424814, 20.673019711422043,
             29.729616427543093, 37.55442387982917, 125.32824271647245,
             135.77785701559],
            [0.00026618116484864926, -0.0008681885839445673, 0.0014174476376588706,
             -0.0015231308488015433, 0.0010502084585483412, -0.000540825515736969,
             0.00019300900837453404, 3.5348485318019746e-06, 1.1557743338413409e-06,
             6.181548524889021e-07, -3.1316471711835696e-07, 3.989652643111546e-07,
             -2.2656409450964743e-07, 1.2789922739378625e-07, -8.259915063897185e-09,
             1.098662224931808e-08],
            [1.9018217478260242e-06, -0.0004374149293397197, 0.0011782018364791763],
            31.55228058803741, 12.414832272409459);
    }, isOurs: true},
];

// --- Full compute_data replacement ---
function computeDataLocal(a, b) {
    if (a < b) { var t = a; a = b; b = t; }
    if (a <= 0 || b <= 0) return null;

    var KAPPA = 2 / Math.PI;
    var e = (a > b) ? Math.sqrt(1 - (b / a) * (b / a)) : 0;
    var h = (a > b) ? Math.pow((a - b) / (a + b), 2) : 0;

    // Circle case
    if (a === b || e === 0) {
        var P_exact_val = 2 * Math.PI * a;
        var methods_result = [];
        METHODS_JS.forEach(function(m) {
            var P_approx = m.fn(a, b);
            methods_result.push({
                name: m.name,
                perimeter: P_approx,
                perimeter_str: (Math.abs(P_approx) < 1e12) ? P_approx.toFixed(15) : P_approx.toExponential(16),
                error_ppm: P_exact_val > 0 ? Math.abs(P_approx / P_exact_val - 1) * 1e6 : 0,
                is_champion: m.isOurs,
            });
        });
        methods_result.sort(function(a, b) { return a.error_ppm - b.error_ppm; });
        return {
            e: 0, a: a, b: b, c: 0, h: 0,
            ell: b, R: 0, U: 0, R_over_U: Math.PI / 2,
            pi_over_2: Math.PI / 2, eta_max: 0,
            sinh_2eta: 0, kappa: KAPPA,
            P_exact: P_exact_val, P_exact_hp: P_exact_val.toPrecision(16),
            methods: methods_result,
            angular_profile: [], chord_data: [], rapidity_data: [],
            I_f: 0, H_u: 0, info_surplus: 0,
            CV2: Math.PI * Math.PI / 8 - 1,
            CV: Math.sqrt(Math.PI * Math.PI / 8 - 1),
        };
    }

    if (e >= 1) return null;

    var c = a * e;
    var ell = b * b / a;
    var R = c / ell;
    var U = R * KAPPA;
    var eta_max = Math.atanh(e);

    var P_exact_val = exactPerimeter(a, b);

    var methods_result = [];
    METHODS_JS.forEach(function(m) {
        var P_approx, err_ppm;
        try {
            P_approx = m.fn(a, b);
            err_ppm = Math.abs(P_approx / P_exact_val - 1) * 1e6;
        } catch(ex) {
            P_approx = NaN;
            err_ppm = NaN;
        }
        methods_result.push({
            name: m.name,
            perimeter: P_approx,
            perimeter_str: (Math.abs(P_approx) < 1e12) ? P_approx.toFixed(15) : P_approx.toExponential(16),
            error_ppm: err_ppm,
            is_champion: m.isOurs,
        });
    });
    methods_result.sort(function(x, y) {
        var a2 = isFinite(x.error_ppm) ? x.error_ppm : Infinity;
        var b2 = isFinite(y.error_ppm) ? y.error_ppm : Infinity;
        return a2 - b2;
    });

    // Angular profile
    var angular_profile = [];
    for (var deg = 0; deg <= 360; deg++) {
        var alpha = deg * Math.PI / 180;
        angular_profile.push([deg, Math.abs(Math.cos(alpha)) * R, Math.abs(Math.cos(alpha)) * Math.PI / 2]);
    }

    // Focal chord data
    var chord_data = [];
    for (var deg2 = 0; deg2 <= 180; deg2 += 5) {
        var alpha2 = deg2 * Math.PI / 180;
        var ecos = e * Math.cos(alpha2);
        var rho1 = (1 + ecos) > 0 ? ell / (1 + ecos) : 1e10;
        var rho2 = (1 - ecos) > 0 ? ell / (1 - ecos) : 1e10;
        var hm = (rho1 + rho2) > 0 ? 2 * rho1 * rho2 / (rho1 + rho2) : 0;
        var MD = (a * a * e / (b * b)) * Math.abs(Math.cos(alpha2));
        chord_data.push({angle: deg2, rho1: rho1, rho2: rho2, harmonic_mean: hm, MD: MD});
    }

    // Rapidity data
    var rapidity_data = [];
    for (var deg3 = 0; deg3 <= 360; deg3++) {
        var theta = deg3 * Math.PI / 180;
        var cos_t = Math.cos(theta);
        var e_cos = e * cos_t;
        var delta, eta;
        if (Math.abs(e_cos) < 1) {
            delta = (1 - e_cos) / (1 + e_cos);
            eta = Math.abs(e_cos) < 0.9999 ? Math.atanh(e_cos) : (e_cos > 0 ? 5 : -5);
        } else {
            delta = 0;
            eta = e_cos > 0 ? 5 : -5;
        }
        rapidity_data.push({theta: deg3, delta: delta, eta: eta, sqrt_delta: Math.sqrt(Math.max(delta, 0))});
    }

    var I_f = R > 0 ? Math.log2(R) : -Infinity;
    var H_u = U > 0 ? Math.log2(U) : -Infinity;

    return {
        e: e, a: a, b: b, c: c, h: h,
        ell: ell, R: R, U: U,
        R_over_U: U > 0 ? R / U : Infinity,
        pi_over_2: Math.PI / 2,
        eta_max: eta_max,
        sinh_2eta: Math.sinh(2 * eta_max),
        kappa: KAPPA,
        P_exact: P_exact_val,
        P_exact_hp: P_exact_val.toPrecision(16),
        methods: methods_result,
        angular_profile: angular_profile,
        chord_data: chord_data,
        rapidity_data: rapidity_data,
        I_f: I_f, H_u: H_u,
        info_surplus: I_f - H_u,
        CV2: Math.PI * Math.PI / 8 - 1,
        CV: Math.sqrt(Math.PI * Math.PI / 8 - 1),
    };
}
"""

# =========================================================================
# Build the static HTML
# =========================================================================

def main():
    output_path = 'index.html'
    if '--output' in sys.argv:
        idx = sys.argv.index('--output')
        if idx + 1 < len(sys.argv):
            output_path = sys.argv[idx + 1]

    print("Building static HTML...")

    # Get the HTML template and pre-computed data from the demo module
    html = demo.HTML_PAGE

    # Do all the placeholder replacements (same as the server does)
    html = html.replace('SWEEP_DATA_PLACEHOLDER', json.dumps(demo.SWEEP_DATA))
    html = html.replace('ERROR_SWEEP_PLACEHOLDER', json.dumps(demo.ERROR_SWEEP))
    html = html.replace('MAX_ERRORS_PLACEHOLDER', json.dumps(demo.MAX_ERRORS))
    html = html.replace('FORMULA_INFO_PLACEHOLDER', json.dumps(demo.FORMULA_INFO))
    html = html.replace('SIGNED_SWEEP_PLACEHOLDER', json.dumps(demo.SIGNED_SWEEP))
    html = html.replace('FORMULA_HTML_PLACEHOLDER', json.dumps(demo.FORMULA_HTML))
    html = html.replace('FORMULA_LATEX_PLACEHOLDER', json.dumps(demo.FORMULA_LATEX))
    html = html.replace('WINNER_DATA_PLACEHOLDER', json.dumps(demo.WINNER_DATA))

    # Inject JS_FORMULAS BEFORE "// Initial render" so METHODS_JS and
    # computeDataLocal are defined before fetchAndRender is called.
    boot_marker = '// Initial render\nfetchAndRender'
    boot_pos = html.find(boot_marker)
    if boot_pos == -1:
        print("ERROR: Could not find '// Initial render' marker in template")
        sys.exit(1)
    html = html[:boot_pos] + JS_FORMULAS + '\n\n' + html[boot_pos:]
    print(f"  Injected JS_FORMULAS before initial render")

    # Replace the fetch call with local computation
    old_fetch = "const resp = await fetch(`/api/compute?a=${a}&b=${b}`);\n    if (seq !== fetchSeq) return; // stale response, discard\n    currentData = await resp.json();"
    new_fetch = "currentData = computeDataLocal(a, b);\n    if (seq !== fetchSeq || !currentData) return;"
    if old_fetch not in html:
        # Try with different whitespace
        import re
        pattern = r"const resp = await fetch\([^)]+\);\s*if \(seq !== fetchSeq\) return;[^\n]*\n\s*currentData = await resp\.json\(\);"
        match = re.search(pattern, html)
        if match:
            html = html[:match.start()] + new_fetch + html[match.end():]
            print("  Replaced fetch call (regex match)")
        else:
            print("WARNING: Could not find fetch call to replace!")
            print("  You may need to manually replace the fetch('/api/compute') call")
    else:
        html = html.replace(old_fetch, new_fetch)
        print("  Replaced fetch call (exact match)")

    # Write output
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(html)

    size_mb = os.path.getsize(output_path) / 1e6
    print(f"\nDone! Static demo written to: {output_path} ({size_mb:.1f} MB)")
    print(f"Open in browser: file://{os.path.abspath(output_path)}")
    print(f"\nPrecision: Pre-computed data uses mpmath (50 digits).")
    print(f"           Live computation uses JS float64 AGM (15+ digits).")
    print(f"           Error display reliable to 0.001 ppb.")


if __name__ == '__main__':
    main()
