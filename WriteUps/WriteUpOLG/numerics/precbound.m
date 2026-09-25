% What must a precautionary bound achieve?
%   g_risk = g_CE + P with P = c0_CE - c0_risk >= 0 the precautionary consumption reduction.
%   Theorem 1 at the state (secant form, r1 -> r2) needs
%        P(R1) - P(R2)  <=  g_CE(R2) - g_CE(R1)  =: margin.
%   Three candidate bounds, in order of how little they need:
%     (a) drop P(R2):            P(R1) <= margin                      [needs only a LEVEL bound]
%     (b) multiplicative:        (1 - theta) P(R1) <= margin, theta <= P(R2)/P(R1)
%     (c) the sandwich's level bound on P: P <= kap_k * H_k
function precbound
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
ag=[0; exp(linspace(log(1e-4),log(600),2999))'];
r1=0.04; r2=0.06;
fprintf(' gam |  P(R1)   P(R2)  | P1-P2  | margin | (a) P1<=marg | theta true | theta needed | kapH\n');
for gam=[1 2 2.5 3 3.2 3.39]
  c0ce1=detc(1+r1,beta,gam,ypath); c0ce2=detc(1+r2,beta,gam,ypath);
  c=egm(1+r1,beta,gam,y,Pi,ag,J); c0r1=c{J}(1,nz);
  c=egm(1+r2,beta,gam,y,Pi,ag,J); c0r2=c{J}(1,nz);
  P1=c0ce1-c0r1; P2=c0ce2-c0r2;
  marg=(ypath(1)-c0ce2)-(ypath(1)-c0ce1);     % g_CE(R2) - g_CE(R1)
  th=P2/P1; thneed=1-marg/P1;
  kap=mpc(1+r1,beta,gam,J); H=hw(Pi,y,1+r1,J);
  kH=kap(J)*H(nz,J);
  if P1<=marg, va='PASS'; else, va='fail'; end
  fprintf(' %4.2f | %7.4f %7.4f | %6.4f | %6.4f |     %s     | %10.4f | %12.4f | %6.3f\n',...
          gam,P1,P2,P1-P2,marg,va,th,thneed,kH);
end
fprintf('\n theta needed is the largest admissible P(R2)/P(R1); the true ratio must exceed it.\n');
fprintf(' kapH is the sandwich level bound on P at (a=0,z_max) -- compare with P(R1).\n');
end
function c0=detc(R,beta,gam,ypath)
J=numel(ypath); t=(0:J-1)';
W=sum(ypath.*R.^(-t)); D=sum(beta.^(t/gam).*R.^(t/gam-t)); c0=W/D;
end
function k=mpc(R,beta,gam,J)
Th=(beta*R)^(1/gam); k=zeros(J,1); k(1)=1;
for j=1:J-1, k(j+1)=k(j)*R/(Th+k(j)*R); end
end
function H=hw(Pi,y,R,J)
nz=numel(y); H=zeros(nz,J); for k=1:J-1, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
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
