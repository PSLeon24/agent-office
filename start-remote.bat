@echo off
rem Agent Office for the Orca host that actually runs the sessions.
rem The dashboard reads ~/.orca/agent-session-journal.db on that host, and this PC
rem reaches it through an SSH tunnel, so the page stays on 127.0.0.1.
rem server.py exits by itself when a copy is already answering on the port.
setlocal
if "%HOST%"=="" set HOST=me@my-orca-host
if "%RPORT%"=="" set RPORT=18765
if "%LPORT%"=="" set LPORT=8766

rem 1) Start the dashboard on the Orca host when it is not already running.
start "Agent Office Remote" /min ssh -n %HOST% "cd ~/agent-office && setsid python3 server.py %RPORT% --no-browser </dev/null >/tmp/agent-office.log 2>&1 &"

rem 2) Forward the remote page to this PC.
start "Agent Office Tunnel" /min ssh -N -o ExitOnForwardFailure=yes -L %LPORT%:127.0.0.1:%RPORT% %HOST%

rem 3) Open it.
timeout /t 3 /nobreak >nul
start "" http://127.0.0.1:%LPORT%/
