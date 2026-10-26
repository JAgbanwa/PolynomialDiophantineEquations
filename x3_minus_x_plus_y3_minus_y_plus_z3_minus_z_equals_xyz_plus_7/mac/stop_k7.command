#!/bin/bash
# Stops the k7 search; finished units stay in progress.txt and start_k7.command resumes.
pkill -x k7 && echo "k7 stopped." || echo "k7 was not running."
