#!/usr/bin/env bash
# ============================================================================
#  Ellipse Perimeter World Record — Setup Script (macOS / Linux)
# ============================================================================
#
#  This script:
#    1. Finds or installs Python 3.9+
#    2. Creates an isolated virtual environment (.venv/)
#    3. Installs all dependencies into it
#    4. Offers to launch the web demo immediately
#
#  Usage:
#    chmod +x setup.sh
#    ./setup.sh              # full setup
#    ./setup.sh --run-demo   # setup + launch standalone demo
#    ./setup.sh --run-server # setup + launch full web UI
#    ./setup.sh --verify     # setup + run adversarial benchmark
#
# ============================================================================

set -e

REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
VENV_DIR="$REPO_DIR/.venv"
REQ_FILE="$REPO_DIR/requirements.txt"

# Colors (if terminal supports them)
if [ -t 1 ]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[1;33m'
    BLUE='\033[0;34m'
    BOLD='\033[1m'
    NC='\033[0m'
else
    RED='' GREEN='' YELLOW='' BLUE='' BOLD='' NC=''
fi

info()  { echo -e "${BLUE}[INFO]${NC}  $*"; }
ok()    { echo -e "${GREEN}[OK]${NC}    $*"; }
warn()  { echo -e "${YELLOW}[WARN]${NC}  $*"; }
fail()  { echo -e "${RED}[FAIL]${NC}  $*"; exit 1; }

# ── Header ──────────────────────────────────────────────────────────────────

echo ""
echo -e "${BOLD}============================================================${NC}"
echo -e "${BOLD}  Ellipse Perimeter World Record — Setup${NC}"
echo -e "${BOLD}  0.083 ppm max error | 6.9x over prior art${NC}"
echo -e "${BOLD}============================================================${NC}"
echo ""

# ── Step 1: Find Python 3.9+ ───────────────────────────────────────────────

info "Looking for Python 3.9+ ..."

PYTHON=""
for candidate in python3 python python3.12 python3.11 python3.10 python3.9; do
    if command -v "$candidate" &>/dev/null; then
        version=$("$candidate" -c "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')" 2>/dev/null || echo "0.0")
        major=$(echo "$version" | cut -d. -f1)
        minor=$(echo "$version" | cut -d. -f2)
        if [ "$major" -ge 3 ] && [ "$minor" -ge 9 ]; then
            PYTHON="$candidate"
            ok "Found $candidate ($version)"
            break
        fi
    fi
done

if [ -z "$PYTHON" ]; then
    echo ""
    fail "Python 3.9+ not found. Please install it first:
    macOS:   brew install python@3.12
    Ubuntu:  sudo apt install python3 python3-venv python3-pip
    Fedora:  sudo dnf install python3 python3-pip"
fi

# ── Step 2: Check for venv module ──────────────────────────────────────────

if ! "$PYTHON" -c "import venv" &>/dev/null; then
    warn "Python venv module not found. Attempting to install..."
    if command -v apt &>/dev/null; then
        info "Running: sudo apt install python3-venv"
        sudo apt install -y python3-venv || fail "Could not install python3-venv. Install it manually."
    else
        fail "Python venv module missing. Install it:
    Ubuntu/Debian: sudo apt install python3-venv
    Fedora:        sudo dnf install python3-libs
    macOS:         Should be included with python3 (try: brew install python@3.12)"
    fi
fi

# ── Step 3: Create virtual environment ─────────────────────────────────────

if [ -d "$VENV_DIR" ]; then
    ok "Virtual environment already exists at .venv/"
else
    info "Creating virtual environment at .venv/ ..."
    "$PYTHON" -m venv "$VENV_DIR"
    ok "Virtual environment created"
fi

# ── Step 4: Activate and install ───────────────────────────────────────────

info "Activating virtual environment ..."
source "$VENV_DIR/bin/activate"
ok "Activated: $(which python3)"

info "Upgrading pip ..."
python3 -m pip install --upgrade pip --quiet

info "Installing dependencies ..."
python3 -m pip install -r "$REQ_FILE" --quiet
ok "All dependencies installed"

# ── Step 5: Verify installation ────────────────────────────────────────────

info "Verifying formula works ..."
python3 -c "
import sys
sys.path.insert(0, '$REPO_DIR')
from src.formulas import r2_3exp_v23_champion, exact_perimeter
a, b = 1.0, 0.01
P = r2_3exp_v23_champion(a, b)
Pe = exact_perimeter(a, b)
err = abs(P - Pe) / Pe * 1e6
print(f'  P(1, 0.01) = {P:.12f}  (error: {err:.4f} ppm)')
assert err < 0.1, f'Error too large: {err} ppm'
"
ok "Formula verified (< 0.1 ppm)"

# ── Step 6: Summary ────────────────────────────────────────────────────────

echo ""
echo -e "${BOLD}============================================================${NC}"
echo -e "${GREEN}  Setup complete!${NC}"
echo -e "${BOLD}============================================================${NC}"
echo ""
echo "  To activate the environment in a new terminal:"
echo -e "    ${BOLD}source .venv/bin/activate${NC}"
echo ""
echo "  Available commands (run from this directory):"
echo ""
echo -e "    ${BOLD}python3 demo/ellipse_web_demo.py${NC}"
echo "      Standalone web demo (opens browser at localhost:8080)"
echo ""
echo -e "    ${BOLD}python3 -m uvicorn src.server:app --host 0.0.0.0 --port 8000${NC}"
echo "      Full web UI with REST API (localhost:8000)"
echo ""
echo -e "    ${BOLD}PYTHONPATH=. python3 -m src.verify${NC}"
echo "      Run 3000-case adversarial benchmark"
echo ""
echo -e "    ${BOLD}python3 benchmark/benchmark_v24.py${NC}"
echo "      Full 5000-case benchmark with LaTeX tables"
echo ""
echo -e "    ${BOLD}python3 benchmark/benchmark_v24.py --quick${NC}"
echo "      Quick 500-case check (~1 min)"
echo ""

# ── Step 7: Optional auto-launch ───────────────────────────────────────────

case "${1:-}" in
    --run-demo)
        info "Launching standalone web demo ..."
        cd "$REPO_DIR"
        python3 demo/ellipse_web_demo.py
        ;;
    --run-server)
        info "Launching full web UI ..."
        cd "$REPO_DIR"
        PYTHONPATH="$REPO_DIR" python3 -m uvicorn src.server:app --host 0.0.0.0 --port 8000
        ;;
    --verify)
        info "Running adversarial benchmark ..."
        cd "$REPO_DIR"
        PYTHONPATH="$REPO_DIR" python3 -m src.verify
        ;;
    "")
        # Interactive prompt
        echo -e "  ${YELLOW}Want to launch something now?${NC}"
        echo "    1) Standalone web demo (recommended for first look)"
        echo "    2) Full web UI (FastAPI + REST API)"
        echo "    3) Run adversarial benchmark"
        echo "    4) Exit"
        echo ""
        read -p "  Choose [1-4]: " choice
        case "$choice" in
            1)
                cd "$REPO_DIR"
                python3 demo/ellipse_web_demo.py
                ;;
            2)
                cd "$REPO_DIR"
                PYTHONPATH="$REPO_DIR" python3 -m uvicorn src.server:app --host 0.0.0.0 --port 8000
                ;;
            3)
                cd "$REPO_DIR"
                PYTHONPATH="$REPO_DIR" python3 -m src.verify
                ;;
            *)
                ok "Done. Run ./setup.sh --run-demo anytime to launch."
                ;;
        esac
        ;;
esac
