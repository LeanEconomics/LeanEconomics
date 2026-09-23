% Does StageSlack hold at log (gamma = 1)?
%  R1*E[C'^-g]  <=  R2*E[(C'+D b)^-g] * (1 + D a/c)^g,
%  b = g_{k+1}(a,z;r1), C'(z') = c_k(z',b;r1), c = c_{k+1}(a,z;r1), D = r2-r1.
function slacklog
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,~]=tauchen(rho,sigma,nz);
for gam=[1 2 3]
  fprintf('\n=== gamma = %g ===\n',gam);
  for r1=[0.00 0.02 0.04]
    for D=[0.0001 0.01]
      [worst,kw,aw,zw,frac]=checkslack(r1,D,beta,gam,y,Pi,J);
      fprintf(' r1=%+.2f D=%.4f : min slack margin = %+.4e at k=%d a=%.3f z=%d ; violated %.2f%% of states\n', ...
        r1,D,worst,kw,aw,zw,100*frac);
    end
  end
end
end
function [worst,kw,aw,zw,frac]=checkslack(r1,D,beta,gam,y,Pi,J)
R1=1+r1; R2=1+r1+D; nz=numel(y); na=400;
ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
c=egm(R1,beta,gam,y,Pi,ag,J);      % c{k+1} = consumption with k periods left
m=y'+R1*ag;
worst=inf; kw=-1; aw=-1; zw=-1; nbad=0; ntot=0;
for k=0:J-2                          % stage k+1 uses c{k+2}
  cK1=c{k+2}; b=m-cK1;               % saving at stage k+1, on the grid
  for z=1:nz
    for i=1:na
      bb=b(i,z); cc=cK1(i,z); aa=ag(i);
      if cc<=0, continue; end
      Cp=zeros(nz,1);
      for zp=1:nz
        Cp(zp)=interp1(ag,c{k+1}(:,zp),min(max(bb,ag(1)),ag(end)),'linear','extrap');
      end
      if any(Cp<=0), continue; end
      lhs=R1*sum(Pi(z,:)'.*Cp.^(-gam));
      rhs=R2*sum(Pi(z,:)'.*(Cp+D*bb).^(-gam))*(1+D*aa/cc)^gam;
      marg=(rhs-lhs)/abs(lhs);
      ntot=ntot+1; if marg<0, nbad=nbad+1; end
      if marg<worst, worst=marg; kw=k; aw=aa; zw=z; end
    end
  end
end
frac=nbad/max(ntot,1);
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
