% Why the asset-dependent ceiling resists proof.
% The recursion needs its argument, the saving ceiling, to be increasing in assets. That needs a
% slope bound on assetHumanWealth, and the natural induction needs the power mean to be
% 1-Lipschitz in the sup norm. It is not: with a negative exponent it is superadditive, so a
% uniform shift comes out AMPLIFIED. Measure both the truth and what the crude chain would give.
function slopes
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; r=0.03;
[Pi,y,nu]=tauchen(rho,sigma,nz); R=1+r; Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/R; end
na=400; ag=[0; exp(linspace(log(1e-4),log(600),na-1))'];
Ga=zeros(na,nz,J); amp=0;
for k=0:K-1
  ph=zeros(na,nz);
  for z=1:nz, ph(:,z)=max(0,(1-kap(k+2))*(y(z)+R*ag)-kap(k+2)*Hup(z,k+2)); end
  Gn=zeros(na,nz);
  for z=1:nz
    Gk=zeros(na,nz);
    for w=1:nz
      Gk(:,w)=interp1(ag,Ga(:,w,k+1),min(max(ph(:,z),ag(1)),ag(end)),'linear','extrap');
    end
    X=y'+Gk;
    Mz=(sum(Pi(z,:).*(X.^(-gam)),2)).^(-1/gam);
    amp=max(amp,max(Mz./min(X,[],2)));      % power-mean amplification M / min component
    Gn(:,z)=min(Mz/R,(1/kap(k+2)-1)*(y(z)+R*ag));
  end
  Ga(:,:,k+2)=Gn;
end
% actual slope of assetHumanWealth in a, against the cap slope the induction would need
worst=0; capw=0;
for k=1:K
  for z=1:nz
    s=diff(Ga(:,z,k+1))./diff(ag);
    worst=max(worst,max(s)); capw=max(capw,(1/kap(k+1)-1)*R);
  end
end
fprintf('r=%.2f: largest actual slope of assetHumanWealth in a  %.4f\n',r,worst);
fprintf('        the cap slope the induction needs to stay under %.4f\n',capw);
fprintf('        power-mean amplification M/min over the grid     %.4f\n',amp);
fprintf('        crude chain would allow the slope to grow by     %.4f per age\n',amp);
fprintf('        over %d ages that is a factor %.3e\n',K,amp^K);
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
