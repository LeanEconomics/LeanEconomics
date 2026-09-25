% gamma = 1, level route: P(R1) <= margin is exactly a CONSUMPTION FLOOR at (a=0, z_max).
%   P = c0_CE - c0 <= margin  <=>  c0 >= c0_CE - margin.
% What is required, and what do the available floors give?
function logfloor
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
ag=[0; exp(linspace(log(1e-4),log(600),2999))'];
D=sum(beta.^(0:J-1)); r1=0.04; r2=0.06;
c0ce1=detc(1+r1,beta,gam,ypath); c0ce2=detc(1+r2,beta,gam,ypath);
margin=(ypath(1)-c0ce2)-(ypath(1)-c0ce1);
c=egm(1+r1,beta,gam,y,Pi,ag,J); c0=c{J}(1,nz);
need=c0ce1-margin;
fprintf(' at r=%.2f, a=0, z_max=%.4f :  D=%.4f\n',r1,y(nz),D);
fprintf('   c0_CE            = %.5f\n',c0ce1);
fprintf('   margin           = %.5f\n',margin);
fprintf('   REQUIRED floor   = %.5f   (c0_CE - margin)\n',need);
fprintf('   true c0          = %.5f   -> accuracy demanded %.1f%%\n',c0,100*(c0-need)/c0);
R=1+r1;
kap=zeros(J,1); kap(1)=1; Th=beta*R;
for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Hmin=0; for k=1:J-1, Hmin=(min(y)+Hmin)/R; end
Ha=zeros(nz,1); Hh=zeros(nz,1); varb=0;
for k=1:J-1
  xa=y+Ha; xh=y+Hh;
  st=0;
  for z=1:nz
    w=Pi(z,:)'; AM=w'*xh; HM=1/(w'*(1./xh)); vr=w'*((xh-AM).^2);
    st=max(st,vr/min(xh));                      % exact: AM - HM <= Var/x_min
  end
  varb=varb/R+st/R;
  Ha=(Pi*xa)/R; Hh=1./(Pi*(1./xh))/R;
end
fprintf('\n available floors at that state:\n');
fprintf('   kap*(y_max)                  = %.5f\n',kap(J)*y(nz));
fprintf('   kap*(y_max + H_minEarnings)  = %.5f   (LowerSandwich)   -> %.2fx too small\n',...
        kap(J)*(y(nz)+Hmin),need/(kap(J)*(y(nz)+Hmin)));
fprintf('   (y_max + H_harmonic)/D       = %.5f   (not a valid floor, see below)\n',(y(nz)+Hh(nz))/D);
% the PROVED incidence floor: kap_k (m + Hrisk_k(z)), Hrisk capped state by state
Hr=zeros(nz,1);
for k=1:J-1
  x=y+Hr; pm=zeros(nz,1);
  for z=1:nz
    w=Pi(z,:)'; pm(z)=1/(w'*(1./x));          % power mean, exponent -1 (gamma = 1)
  end
  Hr=min(pm/R,(1/kap(k+1)-1)*y);
end
fprintf('   kap*(y_max + Hrisk_capped)   = %.5f   (Incidence, PROVED floor) -> %.2fx too small\n',...
        kap(J)*(y(nz)+Hr(nz)),need/(kap(J)*(y(nz)+Hr(nz))));
fprintf('   the cap binds at z_max? %s  (pm/R=%.4f vs cap=%.4f)\n',...
        yesno(Hr(nz)<(1/kap(J)-1)*y(nz)-1e-9),Hr(nz),(1/kap(J)-1)*y(nz));
fprintf('\n the iterated-harmonic formula at other states, against the truth:\n');
for z=[1 2 4]
  fprintf('   z=%d : formula %.5f vs true %.5f  %s\n',z,(y(z)+Hh(z))/D,c{J}(1,z),...
     ternary((y(z)+Hh(z))/D<=c{J}(1,z)+1e-9));
end
fprintf('\n arithmetic-harmonic gap: true %.4f ; Var/x_min accumulation %.4f (Kantorovich was 84.4)\n',...
        Ha(nz)-Hh(nz),varb);
end
function s=yesno(b), if b, s='no'; else, s='YES'; end, end
function s=ternary(b), if b, s='(floor holds)'; else, s='(FLOOR VIOLATED)'; end, end
function c0=detc(R,beta,gam,ypath)
J=numel(ypath); t=(0:J-1)';
W=sum(ypath.*R.^(-t)); Dd=sum(beta.^(t/gam).*R.^(t/gam-t)); c0=W/Dd;
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
