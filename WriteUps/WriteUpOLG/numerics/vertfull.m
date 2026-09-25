% Fuller enumeration: every coordinate pinned by one constraint involving itself or a NEIGHBOUR.
% Forward patterns (each j pinned by L_j, U_j, C_{j-1}+lo, C_{j-1}+hi) and backward patterns (each j
% pinned by L_j, U_j, C_{j+1}-hi, C_{j+1}-lo).  4^6 * 2 each way; every candidate is checked against
% all 26 constraints before being scored.
function vertfull
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
PAT=pats(nz);
fprintf(' stage | allowance | enumerated max WITH concavity | verdict | margin\n');
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1; E=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:30:na
      b=b1(i); if b<=0, continue; end
      mm=y+R1*b; kp=kap(k+1);
      L=kp*(mm+Hr(:,k+1)); U=min(kp*(mm+Ha(:,k+1)),mm); L=min(L,U-1e-12);
      w=Pi(z,:)'; dy=diff(y); lo=kp*dy; hi=dy;
      E=max(E,scan(PAT,L,U,lo,hi,w,nz,+1,dy));
      E=max(E,scan(PAT,L,U,lo,hi,w,nz,-1,dy));
    end
  end
  if E<=allow, vd='PASS'; else, vd='fail'; end
  fprintf(' %5d | %9.4f | %29.4f | %s | %5.2fx\n',k,allow,E,vd,allow/E);
end
end
function P=pats(nz)
n=4^(nz-1)*2; P=zeros(n,nz); r=0;
for a=0:1
  for m=0:4^(nz-1)-1
    r=r+1; P(r,1)=a; t=m;
    for j=2:nz, P(r,j)=mod(t,4); t=floor(t/4); end
  end
end
end
function best=scan(P,L,U,lo,hi,w,nz,dir,dy)
best=0;
if dir<0, L=flipud(L); U=flipud(U); t=lo; lo=flipud(-hi); hi=flipud(-t); w=flipud(w); dy=flipud(dy); end
for r=1:size(P,1)
  C=zeros(nz,1); good=true;
  for j=1:nz
    p=P(r,j);
    if j==1
      if p==0, C(1)=L(1); else, C(1)=U(1); end
    else
      switch p
        case 0, C(j)=L(j);
        case 1, C(j)=U(j);
        case 2, C(j)=C(j-1)+lo(j-1);
        case 3, C(j)=C(j-1)+hi(j-1);
      end
    end
    if C(j)<L(j)-1e-10 || C(j)>U(j)+1e-10, good=false; break; end
    if j>1
      d=C(j)-C(j-1);
      if d<lo(j-1)-1e-10 || d>hi(j-1)+1e-10, good=false; break; end
    end
  end
  if good
    % Carroll-Kimball: consumption is CONCAVE in cash on hand, so the slopes dC/dy fall
    sl=diff(C)./abs(dy);
    if dir>0, conc=all(diff(sl)<=1e-10); else, conc=all(diff(sl)>=-1e-10); end
    if conc
      M=1/(w'*(1./C)); best=max(best,w'*((M./C).^2)-1);
    end
  end
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
