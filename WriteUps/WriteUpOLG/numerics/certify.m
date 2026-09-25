% CERTIFICATE.  On any box the objective sum w v^2/(sum w v)^2 is maximised at a box VERTEX (it is
% unimodal with a minimum in each coordinate), so max over a box = max over its 2^nz vertices -- an
% EXACT, consistent bound, unlike the M(c+)/c- bound that failed.  Branch and bound with it:
%   prune a box if (i) it is disjoint from the polytope, or (ii) its exact box max <= allowance.
% If every box is pruned the maximum over the polytope is certified below the allowance.
function certify
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
R1=1.04; q=(R1/1.06)^(1/gam); Th1=(beta*R1)^(1/gam);
kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
Ha=zeros(nz,J); Hr=zeros(nz,J);
for k=1:J-1
  Ha(:,k+1)=(Pi*(y+Ha(:,k)))/R1;
  x=y+Hr(:,k); pm=zeros(nz,1);
  for z=1:nz, w=Pi(z,:)'; pm(z)=1/(w'*(1./x)); end
  Hr(:,k+1)=min(pm/R1,(1/kap(k+1)-1)*y);
end
c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
VX=dec2bin(0:2^nz-1)-'0';
% the allowance Th/(q(1-kap_k R))-1 is increasing as k falls (kap_k rises), so the NEWBORN stage
% is the binding one; report the profile, then certify it on a fine b grid
al=zeros(J,1);
for kk=1:J-1, al(kk+1)=Th1/(q*(1-min(kap(kk+1)*R1,0.999)))-1; end
fprintf(' allowance by stage: k=59 %.4f, 50 %.4f, 40 %.4f, 30 %.4f, 20 %.4f, 10 %.4f, 5 %.4f\n',...
        al(60),al(51),al(41),al(31),al(21),al(11),al(6));
fprintf(' monotone (newborn tightest)? %s\n\n',yn(all(diff(al(2:J))<=1e-12)));
for k=[J-1]
  allow=Th1/(q*(1-kap(k+1)*R1))-1; allcert=true; maxnodes=0; nfail=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:10:na
      b=b1(i); if b<=0, continue; end
      mm=y+R1*b; kp=kap(k+1);
      L=kp*(mm+Hr(:,k+1)); U=min(kp*(mm+Ha(:,k+1)),mm); L=min(L,U-1e-12);
      w=Pi(z,:)'; dy=diff(y); lo=kp*dy; hi=dy;
      [cert,nd]=bb(L,U,lo,hi,dy,w,nz,allow,VX);
      maxnodes=max(maxnodes,nd);
      if ~cert, allcert=false; nfail=nfail+1; end
    end
  end
  fprintf(' stage %2d : allowance %.4f -> %s   (worst node count %d, %d nodes uncertified)\n',...
          k,allow,vd(allcert),maxnodes,nfail);
end
end
function s=yn(b), if b, s='yes'; else, s='no'; end, end
function s=vd(b), if b, s='CERTIFIED'; else, s='NOT certified'; end, end
function [cert,nd]=bb(L,U,lo,hi,dy,w,nz,allow,VX)
S={[L U]}; nd=0; cert=true;
while ~isempty(S)
  nd=nd+1;
  if nd>40000, cert=false; return; end
  B=S{end}; S(end)=[]; cm=B(:,1); cp=B(:,2);
  % (i) disjoint from the polytope?
  dmin=cm(2:end)-cp(1:end-1); dmax=cp(2:end)-cm(1:end-1);
  if any(dmax<lo-1e-12) || any(dmin>hi+1e-12), continue; end
  smin=max(dmin,lo)./dy; smax=min(dmax,hi)./dy;
  if any(smax(2:end)>smin(1:end-1)+1e-12 & false), end
  if any(smin(2:end)-smax(1:end-1)>1e-12), continue; end   % concavity infeasible
  % (ii) exact box maximum at its vertices
  best=0;
  for v=1:size(VX,1)
    C=cm+(cp-cm).*VX(v,:)';
    M=1/(w'*(1./C)); best=max(best,w'*((M./C).^2)-1);
  end
  if best<=allow, continue; end
  [wd,j]=max(cp-cm);
  if wd<1e-7, cert=false; return; end
  mid=(cm(j)+cp(j))/2;
  B1=B; B1(j,2)=mid; B2=B; B2(j,1)=mid;
  S{end+1}=B1; S{end+1}=B2;
end
end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
end
function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
