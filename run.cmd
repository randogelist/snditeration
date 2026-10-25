@echo off
setlocal EnableExtensions
cd /d "%~dp0"
where lake >nul 2>nul
if errorlevel 1 (
  echo ERROR: Lake/Lean 4.33.0 is not available on PATH.
  exit /b 1
)
call lake build Zetahyperbolic
if errorlevel 1 exit /b 1
call lake env lean Zetahyperbolic\Audit.lean
if errorlevel 1 exit /b 1
echo GOODWORKFLOWFRONTIER::GITHUB_SPECTRAL_v0_1_0::AXIOM_AUDIT=PASS
echo GOODWORKFLOWFRONTIER::GITHUB_SPECTRAL_v0_1_0::LEAN_BUILD=PASS
exit /b 0
