# Search layout (sourced by the scripts).
# Chunk c covers |a| in [BASE + c*WIDTH, BASE + (c+1)*WIDTH), both signs of a  (x = 2a).
# Everything below BASE is being covered on the cloud machine.
BASE=20000000000000      # 2e13  (i.e. |x| >= 4e13)
WIDTH=200000000000       # 2e11 per chunk
RES=6                    # chunks with c % RES == 0 are done on the cloud machine; this Mac does the rest
