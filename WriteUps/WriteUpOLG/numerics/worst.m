% Can the bound be sharpened at the WORST next-period earnings state? Decompose the residual gap
% there into (a) the cap, (b) the power mean versus the expectation, (c) what is left.
% "Effective human wealth" of a bound or of the truth at (a,z) is  H_eff = c/kappa - m.
function worst
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; R=1.04; gam=3;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
% three human-wealth recursions: capped power mean, UNcapped power mean, and the expectation
Hc=zeros(nz,J); Hu=zeros(nz,J); He=zeros(nz,J);
for k=1:J-1
  xc=y+Hc(:,k); Hc(:,k+1)=min(((Pi*(xc.^(-gam))).^(-1/gam))/R,(1./kap(k+1)-1).*y);
  xu=y+Hu(:,k); Hu(:,k+1)=((Pi*(xu.^(-gam))).^(-1/gam))/R;
  He(:,k+1)=(Pi*(y+He(:,k)))/R;
end
ag=[0; exp(linspace(log(1e-4),log(600),2499))'];
c=egm(R,beta,gam,y,Pi,ag,J);
A=1.66;  % the saving of a household at zero wealth in the top state
ia=find(ag>=A,1);
fprintf('at next-period assets a=%.3f, stage 58, effective human wealth H_eff = c/kappa - m:\n',ag(ia));
fprintf('   z |   m   | true c | H_eff(true) | H capped | H uncapped | H expected | bound/truth\n');
for z=1:nz
  m=y(z)+R*ag(ia); tc=c{J-1}(ia,z); He_true=tc/kap(J-1)-m;
  fprintf(' %3d | %5.2f | %6.4f | %11.3f | %8.3f | %10.3f | %10.3f | %11.3f\n',...
    z,m,tc,He_true,Hc(z,J-1),Hu(z,J-1),He(z,J-1),kap(J-1)*(m+Hc(z,J-1))/tc);
end
fprintf('\n the worst state is z=1. There the truth sits between the power mean and the\n');
fprintf(' expectation, so no Euler-based bound can reach it: the Euler inequality delivers\n');
fprintf(' the power mean, and the remaining distance is the precautionary wedge itself.\n');
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn;
end
end
