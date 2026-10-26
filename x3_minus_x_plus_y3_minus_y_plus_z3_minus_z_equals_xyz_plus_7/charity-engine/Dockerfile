# Container for Charity Engine (or any Docker host). Build from the folder ABOVE this one:
#   docker build -f charity-engine/Dockerfile -t k7search .
# Run work unit 17 (results land in ./out):   docker run --rm -v "$PWD/out:/data" k7search 17
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends gcc libc6-dev && rm -rf /var/lib/apt/lists/*
COPY src/k7.c charity-engine/run_job.sh charity-engine/workunits.txt /opt/k7/
RUN cd /opt/k7 \
 && gcc -O3 -march=x86-64-v2 -o k7_generic k7.c -lm -lpthread \
 && gcc -O3 -march=x86-64-v2 -DK=41 -o k7_41_generic k7.c -lm -lpthread \
 && gcc -O3 -march=x86-64-v4 -mavx512ifma -o k7_ifma k7.c -lm -lpthread \
 && gcc -O3 -march=x86-64-v4 -mavx512ifma -DK=41 -o k7_41_ifma k7.c -lm -lpthread \
 && chmod +x run_job.sh
WORKDIR /data
ENTRYPOINT ["/opt/k7/run_job.sh"]
