@echo off
cd /d "%~dp0"
start "Agent Office" /min py -3 server.py %*
