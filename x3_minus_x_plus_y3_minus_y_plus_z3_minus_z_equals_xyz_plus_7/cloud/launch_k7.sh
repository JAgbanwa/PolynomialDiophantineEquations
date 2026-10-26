#!/bin/bash
# Launch the x^3-x+y^3-y+z^3-z = xyz+7 search (|x+y| from 1e11 to 1e13) on one EC2 instance, from AWS CloudShell.
# Usage:  bash launch_k7.sh [region]        (default region: eu-north-1)
# Needs k7_userdata.sh in the same directory. Shows the plan and asks before launching anything.
set -e
REGION=${1:-eu-north-1}
cd "$(dirname "$0")"
UD=k7_userdata.sh
[ -f "$UD" ] || { echo "k7_userdata.sh not found: upload it to CloudShell first (Actions > Upload file)."; exit 1; }
echo "Account: $(aws sts get-caller-identity --query Account --output text)   Region: $REGION"
QUOTA=$(aws service-quotas get-service-quota --region "$REGION" --service-code ec2 --quota-code L-1216C47A --query Quota.Value --output text 2>/dev/null || echo unknown)
USED=$(aws ec2 describe-instances --region "$REGION" --filters Name=instance-state-name,Values=pending,running --query 'Reservations[].Instances[].[CpuOptions.CoreCount,CpuOptions.ThreadsPerCore]' --output text | awk '{s+=$1*$2} END{print s+0}')
echo "On-demand vCPU quota: $QUOTA   vCPUs already running: $USED"
OFFERED=$(aws ec2 describe-instance-type-offerings --region "$REGION" --location-type region --query 'InstanceTypeOfferings[].InstanceType' --output text | tr '\t' '\n')
TYPE=""; VC=0
for c in c7a.48xlarge:192 c6a.48xlarge:192 c7i.48xlarge:192 c7a.32xlarge:128 c6a.32xlarge:128 c6i.32xlarge:128 c7a.24xlarge:96 c6a.24xlarge:96 c7i.24xlarge:96 \
         c7a.16xlarge:64 c6a.16xlarge:64 c7i.16xlarge:64 c6i.16xlarge:64 c7a.8xlarge:32 c6a.8xlarge:32 c7i.8xlarge:32 c6i.8xlarge:32 \
         c7a.4xlarge:16 c6a.4xlarge:16 c7i.4xlarge:16 c6i.4xlarge:16 c7a.2xlarge:8 c6a.2xlarge:8 c7i.2xlarge:8 c6i.2xlarge:8 c5.2xlarge:8 c5.xlarge:4; do
  t=${c%%:*}; v=${c##*:}
  echo "$OFFERED" | grep -qx "$t" || continue
  if [ "$QUOTA" != unknown ]; then avail=$(awk -v q="$QUOTA" -v u="$USED" 'BEGIN{print int(q-u)}'); [ "$v" -le "$avail" ] || continue; fi
  TYPE=$t; VC=$v; break
done
[ -n "$TYPE" ] || { echo "No instance type fits your vCPU quota ($QUOTA). Request more: Service Quotas > Amazon EC2 > 'Running On-Demand Standard (A, C, D, H, I, M, R, T, Z) instances'."; exit 1; }
PRICE=$(aws pricing get-products --region us-east-1 --service-code AmazonEC2 --filters \
  Type=TERM_MATCH,Field=instanceType,Value=$TYPE Type=TERM_MATCH,Field=regionCode,Value=$REGION Type=TERM_MATCH,Field=operatingSystem,Value=Linux \
  Type=TERM_MATCH,Field=tenancy,Value=Shared Type=TERM_MATCH,Field=preInstalledSw,Value=NA Type=TERM_MATCH,Field=capacitystatus,Value=Used \
  --query 'PriceList[0]' --output text 2>/dev/null | python3 -c "import sys,json; d=json.loads(sys.stdin.read()); t=list(d['terms']['OnDemand'].values())[0]; print(round(float(list(t['priceDimensions'].values())[0]['pricePerUnit']['USD']),3))" 2>/dev/null || echo "?")
case $TYPE in c7a*|c6a*) EFF=$VC ;; *) EFF=$(( VC*6/10 )) ;; esac          # AMD vCPU = full core; Intel vCPU = hyperthread
EST=$(( (520 + EFF - 1) / EFF + 1 )); CAP=$(( EST*2 + 2 ))
WORST=$(python3 -c "print(round(float('$PRICE')*$CAP,2))" 2>/dev/null || echo "?")
echo
echo "PLAN: 1 x $TYPE ($VC vCPU), on-demand, ~\$$PRICE per hour"
echo "      estimated ~$EST h; it stops itself when done, hard stop after $CAP h (worst case ~\$$WORST)"
read -p "Launch it? [y/N] " ok; case "$ok" in y|Y) ;; *) echo "Not launched."; exit 0 ;; esac
sed "s/shutdown -h +480 /shutdown -h +$((CAP*60)) /; s/cap=480min/cap=$((CAP*60))min/" "$UD" | gzip -9 > /tmp/k7_ud.gz
SIZE=$(stat -c %s /tmp/k7_ud.gz); [ "$SIZE" -lt 16384 ] || { echo "user data too large ($SIZE bytes)"; exit 1; }
IID=$(aws ec2 run-instances --region "$REGION" \
  --image-id resolve:ssm:/aws/service/ami-amazon-linux-latest/al2023-ami-kernel-default-x86_64 \
  --instance-type "$TYPE" --count 1 --instance-initiated-shutdown-behavior stop \
  --user-data fileb:///tmp/k7_ud.gz \
  --tag-specifications 'ResourceType=instance,Tags=[{Key=Name,Value=k7-search}]' \
  --query 'Instances[0].InstanceId' --output text)
echo "LAUNCHED $IID ($TYPE, $REGION)"
echo "$IID $REGION" > k7_instance.txt
echo
echo "Progress (every ~5 min):  aws ec2 get-console-output --region $REGION --instance-id $IID --latest --output text | grep K7"
echo "Stop early:               aws ec2 stop-instances --region $REGION --instance-ids $IID"
echo "Delete after results:     aws ec2 terminate-instances --region $REGION --instance-ids $IID"
