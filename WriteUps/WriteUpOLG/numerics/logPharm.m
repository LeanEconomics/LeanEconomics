% gamma = 1: is precautionary saving at (a=0,z) exactly the arithmetic-minus-harmonic human
% wealth gap, divided by D = sum beta^t?  And what does Kantorovich give for that gap?
%   H_arith: H_{k+1}(z) = sum_z' pi(z,z') (y(z')+H_k(z')) / R
%   H_harm : H_{k+1}(z) = [ sum_z' pi(z,z') (y(z')+H_k(z'))^{-1} ]^{-1} / R
%   predicted c0 = (y(z) + H(z)) / D
function logP
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
ag=[0; exp(linspace(log(1e-4),log(600),2999))'];
D=sum(beta.^(0:J-1));
fprintf(' D = %.4f\n\n',D);
for r=[0.04 0.06]
  R=1+r;
  Ha=zeros(nz,1); Hh=zeros(nz,1); kant=0; gapstep=zeros(J,1);
  for k=1:J-1
    xa=y+Ha; xh=y+Hh;
    Ha=(Pi*xa)/R;
    Hh=1./(Pi*(1./xh))/R;
    % per-step Kantorovich bound on AM - HM for the vector xh under pi(z,.)
    st=0;
    for z=1:nz
      w=Pi(z,:)'; idx=w>1e-12; v=xh(idx); ww=w(idx); ww=ww/sum(ww);
      AM=ww'*v; HM=1/(ww'*(1./v)); M=max(v); m=min(v);
      st=max(st,AM*(M-m)^2/(4*M*m));
    end
    gapstep(k)=st; kant=kant/R+st/R;
  end
  c=egm(R,beta,gam,y,Pi,ag,J);
  fprintf(' r=%.2f\n',r);
  fprintf('   z |   H_arith  |   H_harm  | gap  | c0 true | c0 from H_harm | c0 from H_arith\n');
  for z=[1 4 nz]
    fprintf('  %2d | %10.4f | %9.4f |%5.3f | %7.5f | %14.5f | %15.5f\n',...
      z,Ha(z),Hh(z),Ha(z)-Hh(z),c{J}(1,z),(y(z)+Hh(z))/D,(y(z)+Ha(z))/D);
  end
  P=(y(nz)+Ha(nz))/D-c{J}(1,nz);
  fprintf('   at z_max: P (true, vs CE) = %.5f ; (H_arith-H_harm)/D = %.5f\n',P,(Ha(nz)-Hh(nz))/D);
  fprintf('   accumulated Kantorovich bound on the gap = %.4f (true gap %.4f), /D = %.5f\n\n',...
          kant,Ha(nz)-Hh(nz),kant/D);
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
