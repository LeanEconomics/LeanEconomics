% Means-tested pension: is the policy function non-monotone at realistic parameters?
% Deterministic retiree, T periods, CRRA, asset test on CURRENT assets each period.
% Global grid search (the value function is not concave, so no FOC).
function meanstest
r=0.04; R=1+r; beta=0.96; gam=3; T=25; pfull=0.40;   % pension = 40% of mean earnings
cap=3.0;                                              % free-area threshold (mean-income units)
na=6001; ag=linspace(0,25,na)';
cases={ {'lump sum',      @(a) pfull+0*a},                          ...
        {'taper 0.078',   @(a) max(0,pfull-0.078*max(0,a-cap))},    ...
        {'taper 0.50',    @(a) max(0,pfull-0.50 *max(0,a-cap))},    ...
        {'taper 1.20 (>R)',@(a) max(0,pfull-1.20*max(0,a-cap))},    ...
        {'cliff',         @(a) pfull*(a<=cap)} };
for ci=1:numel(cases)
  nm=cases{ci}{1}; pen=cases{ci}{2}; m=R*ag+pen(ag);
  fprintf('\n===== %s : cash on hand monotone? %d (min diff %.4f)\n',nm,all(diff(m)>=0),min(diff(m)));
  V=zeros(na,1); polA=zeros(na,T); polC=zeros(na,T);
  for t=T:-1:1
    if t==T
      c=m; ap=zeros(na,1); Vn=u(c,gam);
    else
      % value of saving ap (grid) = u(m-ap) + beta*V(ap)
      [Vn,ap,c]=deal(zeros(na,1),zeros(na,1),zeros(na,1));
      for k=1:na
        cc=m(k)-ag; ok=cc>1e-10; vals=-inf(na,1); vals(ok)=u(cc(ok),gam)+beta*V(ok);
        [Vn(k),j]=max(vals); ap(k)=ag(j); c(k)=m(k)-ag(j);
      end
    end
    V=Vn; polA(:,t)=ap; polC(:,t)=c;
  end
  for t=[1 5 10 15 20]
    dA=diff(polA(:,t)); dC=diff(polC(:,t));
    iA=find(dA<-1e-9,1); iC=find(dC<-1e-9,1);
    fprintf('  age %2d: saving monotone? %d', t, isempty(iA));
    if ~isempty(iA), fprintf(' (falls at a=%.2f by %.3f)',ag(iA),-min(dA)); end
    fprintf(' | consumption monotone? %d',isempty(iC));
    if ~isempty(iC), fprintf(' (falls at a=%.2f by %.3f)',ag(iC),-min(dC)); end
    fprintf('\n');
  end
end
% worker one period before retirement: continuation = retirement value under the taper
fprintf('\n===== worker just before retirement (taper 0.078 during retirement)\n');
pen=@(a) max(0,pfull-0.078*max(0,a-cap)); m=R*ag+pen(ag); V=u(m,gam);
for t=T-1:-1:1
  Vn=zeros(na,1);
  for k=1:na, cc=m(k)-ag; ok=cc>1e-10; vals=-inf(na,1); vals(ok)=u(cc(ok),gam)+beta*V(ok); Vn(k)=max(vals); end
  V=Vn;
end
mw=R*ag+1.0;      % working: earnings 1, no pension
apw=zeros(na,1); cw=zeros(na,1);
for k=1:na, cc=mw(k)-ag; ok=cc>1e-10; vals=-inf(na,1); vals(ok)=u(cc(ok),gam)+beta*V(ok); [~,j]=max(vals); apw(k)=ag(j); cw(k)=mw(k)-ag(j); end
dA=diff(apw); dC=diff(cw);
fprintf('  saving monotone? %d (max fall %.4f) | consumption monotone? %d (max fall %.4f)\n',all(dA>=-1e-9),-min(dA),all(dC>=-1e-9),-min(dC));
k=find(dA>0.05,1); if ~isempty(k), fprintf('  saving jumps by %.3f at a=%.2f (consumption falls by %.3f)\n',dA(k),ag(k),-dC(k)); end
end
function v=u(c,gam), if gam==1, v=log(c); else v=(c.^(1-gam)-1)/(1-gam); end, end
