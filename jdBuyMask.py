# -*- coding=utf-8 -*-
'''
京东抢购口罩程序
'''
import requests
import time
import json
import sys
import random
from bs4 import BeautifulSoup
from log.jdlogger import logger
from jdemail.jdEmail import sendMail

'''
需要修改
'''
# cookie 网页获取
# cookies_String = ''
cookies_String = 'unpl=V2_ZzNtbUVSREB9ChVceB9fVWJWG1xKUkVAdAkTVikaXQxgBBUOclRCFnQUR1RnGlQUZwUZXkBcRhFFCEdkeB5fA2AFEFlBZxVLK14bADlNDEY1WnwHBAJfFXYPR1Z6EVgBVzMRXXJXQiV9DERXfBtYBmQzIlpyZ3MTdQhFUEsYbARXQUYBR19DFXJFTlB5GlsHYwARbUNnQA%3d%3d; __jdv=76161171|google-search|t_262767352_googlesearch|cpc|kwd-126030955_0_646d93b9272a4d80947d00d3c208666b|1580289825978; areaId=1; shshshfpa=cab4d538-1df8-8449-975c-7e0f4731f855-1580289828; shshshfpb=yrPAVZoFu%20QdOp3DXNHjAMA%3D%3D; __jdu=953263522; PCSYCityID=CN_110000_110100_110115; pinId=DY-HvY35UiVpKJ-Air2rGbV9-x-f3wj7; pin=503352477-283496; unick=z_binks; _tp=U4v4jO%2BOa72eEyELUQ8FA%2BM%2BfEwNfylRzKirGX8j0E0%3D; _pst=503352477-283496; user-key=fa9abec0-c642-4f82-9821-be44364e7838; ipLoc-djd=1-2810-6501-0.137925768; ipLocation=%u5317%u4eac; cn=3; TrackID=1zrarohWKHXuUMwH3g8iNWm1RXJhmfcfj4Xm-L2iv1Bvr5uVulxpzWajvt_d-aWHUIMd-45JCwjamZYpJTXdxd0B4wQrFJq936nQHwibdf84; thor=F02DCBE38B3B3E82405687F829D9F8C2CC732DE05395E742D82CE94CC9E66A5D56C16209046FB663069CE51D6FC02542641C0DA1F5143FE6DA88A10C43D72640FFD8EA23EC96DA42048ABB63EB978CC188CAC94304BF6737DA71E1D82B65C5AE060725481E341C4F3EAE29574DD2362F2E49248F2F948901CDC1A4DE9BDC5701BC496570E8275F85DFDC8F8FEEABE92881096181912358C7E8BAB7F2E1B03BCC; ceshi3.com=201; shshshfp=641dd281fbd9ac6cca28336768b100f6; shshshsID=1f8925935c81d541103abdd27d58c9bb_1_1581149046281; __jda=122270672.953263522.1580289825.1581083461.1581149022.6; __jdb=122270672.7.953263522|6.1581149022; __jdc=122270672; 3AB9D23F7A4B3C9B=YQBXU3IDIGOFVE5I6PFGVAZ4WQX4FYTHPKAE24JMIPAAO3K73XWKCYBPGHNQ27P7MX6RRXQSJESZL6MXM7EJFPTQKQ'
# 有货通知 收件邮箱
mail = 'zbinks@126.com'
# 商品的url
url = {
    'https://c0.3.cn/stock?skuId=1835967&area=16_1362_44319_51500&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery1535213',
    'https://c0.3.cn/stock?skuId=1835968&area=16_1362_44319_51500&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery366840',
    'https://c0.3.cn/stock?skuId=1336984&area=16_1362_44319_51500&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery94700',
    'https://c0.3.cn/stock?skuId=65466451629&area=16_1362_44319_51500&venderId=127922&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery8432226',
    'https://c0.3.cn/stock?skuId=7498169&area=16_1362_44319_51500&venderId=1000128491&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery7323892',
    'https://c0.3.cn/stock?skuId=7263128&area=16_1362_44319_51500&venderId=1000128491&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery9621467',
    'https://c0.3.cn/stock?skuId=4061438&area=16_1362_44319_51500&venderId=1000005584&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery620656',
    'https://c0.3.cn/stock?skuId=65421329578&area=16_1362_44319_51500&venderId=593210&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery4952468',
    'https://c0.3.cn/stock?skuId=100005678825&area=16_1362_44319_51500&venderId=1000090691&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery2192795',
    'https://c0.3.cn/stock?skuId=100005294853&area=16_1362_44319_51500&venderId=1000090691&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery8766944',
    'https://c0.3.cn/stock?skuId=45923412989&area=16_1362_44319_51500&venderId=10066244&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery8072251',
    'https://c0.3.cn/stock?skuId=62830056100&area=16_1362_44319_51500&venderId=10066244&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery599501',
    'https://c0.3.cn/stock?skuId=45006657879&area=16_1362_44319_51500&venderId=10066244&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_77a8935fb872d&pduid=526700225&ch=1&callback=jQuery6257903',
    'https://c0.3.cn/stock?skuId=1336984&area=1_72_2799_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=1035427354&ch=1&callback=jQuery530569',
    'https://c0.3.cn/stock?skuId=1306182&area=1_72_2799_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=1035427354&ch=1&callback=jQuery6572795',
    'https://c0.3.cn/stock?skuId=2582352&area=1_72_2799_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=1035427354&ch=1&callback=jQuery7637686',
    'https://c0.3.cn/stock?skuId=1835968&area=1_72_2799_0&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=1035427354&ch=1&callback=jQuery6965677',
    'https://c0.3.cn/stock?skuId=1835967&area=1_72_2799_0&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=1035427354&ch=1&callback=jQuery3911758',
    'https://c0.3.cn/stock?skuId=3649920&area=1_72_2799_0&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=1035427354&ch=1&callback=jQuery3239457',
    'https://c0.3.cn/stock?skuId=100011303188&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery6431712',
    'https://c0.3.cn/stock?skuId=4954677&area=1_72_2799_0&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=1035427354&ch=1&callback=jQuery9906168',
    'https://c0.3.cn/stock?skuId=65421329578&area=1_72_2799_0&venderId=593210&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery587338',
    'https://c0.3.cn/stock?skuId=100009443324&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery1225480',
    'https://c0.3.cn/stock?skuId=100011303176&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery7895873',
    'https://c0.3.cn/stock?skuId=100011303220&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery2336685',
    'https://c0.3.cn/stock?skuId=100011303174&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery4887760',
    'https://c0.3.cn/stock?skuId=100011303172&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery4305892',
    'https://c0.3.cn/stock?skuId=100011303180&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery6552283',
    'https://c0.3.cn/stock?skuId=100011303188&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery6431712',
    'https://c0.3.cn/stock?skuId=100011303190&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=&pduid=2102363655&ch=1&callback=jQuery6063461',
    'https://c0.3.cn/stock?skuId=19028117913&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5241326',
    'https://c0.3.cn/stock?skuId=19028117914&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery720832',
    'https://c0.3.cn/stock?skuId=19028117912&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2554735',
    'https://c0.3.cn/stock?skuId=19028117915&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2671403',
    'https://c0.3.cn/stock?skuId=1835967&area=1_2810_6501_0&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2029801',
    'https://c0.3.cn/stock?skuId=1835968&area=1_2810_6501_0&venderId=1000084390&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5822412',
    'https://c0.3.cn/stock?skuId=10183475858&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery3103540',
    'https://c0.3.cn/stock?skuId=10183475859&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2825161',
    'https://c0.3.cn/stock?skuId=65425816569&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery6822581',
    'https://c0.3.cn/stock?skuId=65425816570&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery644034',
    'https://c0.3.cn/stock?skuId=1614629784&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery8035091',
    'https://c0.3.cn/stock?skuId=1614629785&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1481972',
    'https://c0.3.cn/stock?skuId=1614629787&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery3845097',
    'https://c0.3.cn/stock?skuId=1614629788&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1923236',
    'https://c0.3.cn/stock?skuId=65424912828&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery6659973',
    'https://c0.3.cn/stock?skuId=65424912829&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7785736',
    'https://c0.3.cn/stock?skuId=10184106420&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1603016',
    'https://c0.3.cn/stock?skuId=65424587534&area=1_2810_6501_0&venderId=117784&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9592356',
    'https://c0.3.cn/stock?skuId=14111477461&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7876756',
    'https://c0.3.cn/stock?skuId=14111477460&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1425729',
    'https://c0.3.cn/stock?skuId=14111477462&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery8599979',
    'https://c0.3.cn/stock?skuId=14111477463&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5234505',
    'https://c0.3.cn/stock?skuId=23471980414&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery6026727',
    'https://c0.3.cn/stock?skuId=23471980415&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery6308786',
    'https://c0.3.cn/stock?skuId=38495731611&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery3851681',
    'https://c0.3.cn/stock?skuId=38495731612&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7327584',
    'https://c0.3.cn/stock?skuId=13074578910&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5455858',
    'https://c0.3.cn/stock?skuId=13074578911&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery629676',
    'https://c0.3.cn/stock?skuId=14669666226&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2371034',
    'https://c0.3.cn/stock?skuId=14669666228&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery6821046',
    'https://c0.3.cn/stock?skuId=14669666225&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1470257',
    'https://c0.3.cn/stock?skuId=14669666227&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2884216',
    'https://c0.3.cn/stock?skuId=14198371126&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery4872377',
    'https://c0.3.cn/stock?skuId=14198371125&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery611775',
    'https://c0.3.cn/stock?skuId=14198371127&area=1_2810_6501_0&venderId=683964&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9231535',
    'https://c0.3.cn/stock?skuId=4756045&area=1_2810_6501_0&venderId=0&buyNum=1&choseSuitSkuIds=&cat=1620,1624,1661&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery8419382',
    'https://c0.3.cn/stock?skuId=5365064&area=1_2810_6501_0&venderId=0&buyNum=1&choseSuitSkuIds=&cat=1620,1624,1661&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5257455',
    'https://c0.3.cn/stock?skuId=100005151507&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery883009',
    'https://c0.3.cn/stock?skuId=100005818743&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery8699493',
    'https://c0.3.cn/stock?skuId=100006066047&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2879039',
    'https://c0.3.cn/stock?skuId=100010638508&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery4184092',
    'https://c0.3.cn/stock?skuId=100009445348&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5865839',
    'https://c0.3.cn/stock?skuId=100009441994&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery8196105',
    'https://c0.3.cn/stock?skuId=100009442472&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9818790',
    'https://c0.3.cn/stock?skuId=100006992566&area=1_2810_6501_0&venderId=1000164426&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1995623',
    'https://c0.3.cn/stock?skuId=100004092119&area=1_2810_6501_0&venderId=1000164426&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2341974',
    'https://c0.3.cn/stock?skuId=100004092127&area=1_2810_6501_0&venderId=1000164426&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5565005',
    'https://c0.3.cn/stock?skuId=100006992518&area=1_2810_6501_0&venderId=1000164426&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7220685',
    'https://c0.3.cn/stock?skuId=100004092113&area=1_2810_6501_0&venderId=1000164426&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery4450900',
    'https://c0.3.cn/stock?skuId=100004447723&area=1_2810_6501_0&venderId=1000282483&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7268044',
    'https://c0.3.cn/stock?skuId=100002340330&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery3327582',
    'https://c0.3.cn/stock?skuId=100002956964&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery2533731',
    'https://c0.3.cn/stock?skuId=100002068063&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery7507866',
    'https://c0.3.cn/stock?skuId=100002641826&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery9653201',
    'https://c0.3.cn/stock?skuId=100001998331&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery7928611',
    'https://c0.3.cn/stock?skuId=100002072425&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery6485740',
    'https://c0.3.cn/stock?skuId=7764518&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery6571947',
    'https://c0.3.cn/stock?skuId=7764520&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery3122631',
    'https://c0.3.cn/stock?skuId=100002641694&area=1_2810_6501_0&venderId=1000104644&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=953263522&pdpin=503352477-283496&detailedAdd=null&callback=jQuery4620169',
    'https://c0.3.cn/stock?skuId=48386659214&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1962397',
    'https://c0.3.cn/stock?skuId=48386659215&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery5539862',
    'https://c0.3.cn/stock?skuId=48386659216&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9132194',
    'https://c0.3.cn/stock?skuId=48386659217&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery3695714',
    'https://c0.3.cn/stock?skuId=11106544810&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9169253',
    'https://c0.3.cn/stock?skuId=1581140940&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery3918692',
    'https://c0.3.cn/stock?skuId=1581140941&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery8389974',
    'https://c0.3.cn/stock?skuId=11107520301&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9873434',
    'https://c0.3.cn/stock?skuId=18724980667&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9223743',
    'https://c0.3.cn/stock?skuId=18724980668&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7851813',
    'https://c0.3.cn/stock?skuId=18724980669&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2215851',
    'https://c0.3.cn/stock?skuId=11108141699&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery4031657',
    'https://c0.3.cn/stock?skuId=31814638527&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7314566',
    'https://c0.3.cn/stock?skuId=31764120734&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery2603915',
    'https://c0.3.cn/stock?skuId=31764120735&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery3408108',
    'https://c0.3.cn/stock?skuId=20826949214&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery1772913',
    'https://c0.3.cn/stock?skuId=20826949215&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery9852726',
    'https://c0.3.cn/stock?skuId=1597682782&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery6278925',
    'https://c0.3.cn/stock?skuId=11106544810&area=1_2810_6501_0&venderId=145557&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=503352477-283496&pduid=953263522&ch=1&callback=jQuery7890980'


    # 'https://c0.3.cn/stock?skuId=1336984&area=19_1607_4773_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=1580535906442142991701&ch=1&callback=jQuery6715489',
    # 'https://c0.3.cn/stock?skuId=4642656&area=19_1607_4773_0&venderId=1000006724&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=1580535906442142991701&ch=1&callback=jQuery4552086',
    # 'https://c0.3.cn/stock?skuId=65466451629&area=19_1607_4773_0&venderId=127922&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=1580535906442142991701&ch=1&callback=jQuery2790674',
    # 'https://c0.3.cn/stock?skuId=65437208345&area=19_1607_4773_0&venderId=127922&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=1580535906442142991701&ch=1&callback=jQuery1749958',
    # 'https://c0.3.cn/stock?skuId=7498169&area=19_1607_4773_0&venderId=1000128491&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=15631231857651045904648&ch=1&callback=jQuery4102801',
    # 'https://c0.3.cn/stock?skuId=7498165&area=19_1607_4773_0&venderId=1000128491&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=15631231857651045904648&ch=1&callback=jQuery9614479',
    'https://c0.3.cn/stock?skuId=7263128&area=19_1607_4773_0&venderId=1000128491&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=15631231857651045904648&ch=1&callback=jQuery8872960',
    # 'https://c0.3.cn/stock?skuId=1739089&area=19_1607_4773_0&venderId=1000017287&buyNum=1&choseSuitSkuIds=&cat=15248,15250,15278&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=jd_7c3992aa27d1a&pduid=1580535906442142991701&ch=1&callback=jQuery4479703'
    'https://c0.3.cn/stock?skuId=1337002&area=1_72_2799_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7277764'
    'https://c0.3.cn/stock?skuId=2582352&area=1_72_2799_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4919741'
    'https://c0.3.cn/stock?skuId=1336984&area=1_72_2799_0&venderId=1000078145&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5568297'
    'https://c0.3.cn/stock?skuId=100009443324&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5104704'
    'https://c0.3.cn/stock?skuId=100010233106&area=1_72_2799_0&venderId=1000084542&buyNum=3&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3799242'
    'https://c0.3.cn/stock?skuId=100006784140&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7458938'
    'https://c0.3.cn/stock?skuId=100003973898&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5854086'
    'https://c0.3.cn/stock?skuId=100003988835&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9941712'
    'https://c0.3.cn/stock?skuId=100000380689&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5475657'
    'https://c0.3.cn/stock?skuId=100011303174&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery382720'
    'https://c0.3.cn/stock?skuId=100003018321&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery6573818'
    'https://c0.3.cn/stock?skuId=100004849402&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery927091'
    'https://c0.3.cn/stock?skuId=100011303172&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7099571'
    'https://c0.3.cn/stock?skuId=100011303176&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9722922'
    'https://c0.3.cn/stock?skuId=100006252939&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery1504924'
    'https://c0.3.cn/stock?skuId=100011303180&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3136958'
    'https://c0.3.cn/stock?skuId=100011303190&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery635774'
    'https://c0.3.cn/stock?skuId=18306971150&area=1_72_2799_0&venderId=663284&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5786790'
    'https://c0.3.cn/stock?skuId=100006153637&area=1_72_2799_0&venderId=1000092342&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=2102363655&pdpin=1615272479_m&detailedAdd=null&callback=jQuery2438819'''
    'https://c0.3.cn/stock?skuId=100011107634&area=1_72_2799_0&venderId=1000092342&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=2102363655&pdpin=1615272479_m&detailedAdd=null&callback=jQuery1856614'''
    'https://c0.3.cn/stock?skuId=100011197920&area=1_72_2799_0&venderId=1000092342&cat=14065,14099,14103&buyNum=5&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=2102363655&pdpin=1615272479_m&detailedAdd=null&callback=jQuery6900665'''
    'https://c0.3.cn/stock?skuId=100011341640&area=1_72_2799_0&venderId=1000108181&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery881321'''
    'https://c0.3.cn/stock?skuId=100011290074&area=1_72_2799_0&venderId=1000108181&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery6896194'''
    'https://c0.3.cn/stock?skuId=11609507800&area=1_72_2799_0&venderId=656282&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery782914'''
    'https://c0.3.cn/stock?skuId=10554550907&area=1_72_2799_0&venderId=597521&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4313493'''
    'https://c0.3.cn/stock?skuId=4993437&area=1_72_2799_0&venderId=0&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9558125'''
    'https://c0.3.cn/stock?skuId=49007827200&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7852843'''
    'https://c0.3.cn/stock?skuId=49007827199&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5059702'
    'https://c0.3.cn/stock?skuId=49007836701&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8757675'
    'https://c0.3.cn/stock?skuId=49007836702&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5656598'
    'https://c0.3.cn/stock?skuId=49007836703&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9261188'
    'https://c0.3.cn/stock?skuId=49007836704&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4034059'
    'https://c0.3.cn/stock?skuId=49007836705&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9960274'
    'https://c0.3.cn/stock?skuId=49007836706&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9357125'
    'https://c0.3.cn/stock?skuId=49007836707&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8336220'
    'https://c0.3.cn/stock?skuId=49007836708&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8799267'
    'https://c0.3.cn/stock?skuId=49007836709&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5748418'
    'https://c0.3.cn/stock?skuId=49007836710&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4443309'
    'https://c0.3.cn/stock?skuId=49007836711&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery1147512'
    'https://c0.3.cn/stock?skuId=49007836712&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8555459'
    'https://c0.3.cn/stock?skuId=49007836713&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery1600259'
    'https://c0.3.cn/stock?skuId=49007836714&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7189779'
    'https://c0.3.cn/stock?skuId=49007836715&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery2268663'
    'https://c0.3.cn/stock?skuId=49007836716&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3299226'
    'https://c0.3.cn/stock?skuId=8508919&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery2108512'
    'https://c0.3.cn/stock?skuId=8010807&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery2062568'
    'https://c0.3.cn/stock?skuId=8296344&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3244829https://c0.3.cn/stock?skuId=100010233106&area=1_72_2799_0&venderId=1000084542&buyNum=3&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3799242'''
    'https://c0.3.cn/stock?skuId=100006784140&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7458938'
    'https://c0.3.cn/stock?skuId=100003973898&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5854086'
    'https://c0.3.cn/stock?skuId=100003988835&area=1_72_2799_0&venderId=1000084542&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9941712'
    'https://c0.3.cn/stock?skuId=100000380689&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5475657'
    'https://c0.3.cn/stock?skuId=100011303174&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery382720'
    'https://c0.3.cn/stock?skuId=100003018321&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery6573818'
    'https://c0.3.cn/stock?skuId=100004849402&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery927091'
    'https://c0.3.cn/stock?skuId=100011303172&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7099571'
    'https://c0.3.cn/stock?skuId=100011303176&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9722922'
    'https://c0.3.cn/stock?skuId=100006252939&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery1504924'
    'https://c0.3.cn/stock?skuId=100011303180&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3136958'
    'https://c0.3.cn/stock?skuId=100011303190&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery635774'
    'https://c0.3.cn/stock?skuId=18306971150&area=1_72_2799_0&venderId=663284&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5786790'
    'https://c0.3.cn/stock?skuId=100006153637&area=1_72_2799_0&venderId=1000092342&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=2102363655&pdpin=1615272479_m&detailedAdd=null&callback=jQuery2438819'
    'https://c0.3.cn/stock?skuId=100011107634&area=1_72_2799_0&venderId=1000092342&cat=14065,14099,14103&buyNum=1&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=2102363655&pdpin=1615272479_m&detailedAdd=null&callback=jQuery1856614'
    'https://c0.3.cn/stock?skuId=100011197920&area=1_72_2799_0&venderId=1000092342&cat=14065,14099,14103&buyNum=5&choseSuitSkuIds=&extraParam={%22originid%22:%221%22}&ch=1&fqsp=0&pduid=2102363655&pdpin=1615272479_m&detailedAdd=null&callback=jQuery6900665'
    'https://c0.3.cn/stock?skuId=100011341640&area=1_72_2799_0&venderId=1000108181&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery881321'
    'https://c0.3.cn/stock?skuId=100011290074&area=1_72_2799_0&venderId=1000108181&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery6896194'
    'https://c0.3.cn/stock?skuId=11609507800&area=1_72_2799_0&venderId=656282&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery782914'
    'https://c0.3.cn/stock?skuId=10554550907&area=1_72_2799_0&venderId=597521&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4313493'
    'https://c0.3.cn/stock?skuId=4993437&area=1_72_2799_0&venderId=0&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9558125'
    'https://c0.3.cn/stock?skuId=49007827200&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7852843'
    'https://c0.3.cn/stock?skuId=49007827199&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5059702'
    'https://c0.3.cn/stock?skuId=49007836701&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8757675'
    'https://c0.3.cn/stock?skuId=49007836702&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5656598'
    'https://c0.3.cn/stock?skuId=49007836703&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9261188'
    'https://c0.3.cn/stock?skuId=49007836704&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4034059'
    'https://c0.3.cn/stock?skuId=49007836705&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9960274'
    'https://c0.3.cn/stock?skuId=49007836706&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery9357125'
    'https://c0.3.cn/stock?skuId=49007836707&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8336220'
    'https://c0.3.cn/stock?skuId=49007836708&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8799267'
    'https://c0.3.cn/stock?skuId=49007836709&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery5748418'
    'https://c0.3.cn/stock?skuId=49007836710&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery4443309'
    'https://c0.3.cn/stock?skuId=49007836711&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery1147512'
    'https://c0.3.cn/stock?skuId=49007836712&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery8555459'
    'https://c0.3.cn/stock?skuId=49007836713&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery1600259'
    'https://c0.3.cn/stock?skuId=49007836714&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery7189779'
    'https://c0.3.cn/stock?skuId=49007836715&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery2268663'
    'https://c0.3.cn/stock?skuId=49007836716&area=1_72_2799_0&venderId=10160578&buyNum=1&choseSuitSkuIds=&cat=9192,12190,1517&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3299226'
    'https://c0.3.cn/stock?skuId=8508919&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery2108512'
    'https://c0.3.cn/stock?skuId=8010807&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery2062568'
    'https://c0.3.cn/stock?skuId=8296344&area=1_72_2799_0&venderId=1000135921&buyNum=1&choseSuitSkuIds=&cat=9855,9858,9924&extraParam={%22originid%22:%221%22}&fqsp=0&pdpin=1615272479_m&pduid=2102363655&ch=1&callback=jQuery3244829'
}
'''
备用
'''
timesleep = random.randint(3, 8)

# eid
eid = ''
fp = ''
# 支付密码
payment_pwd = ''

session = requests.session()
session.headers = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
    "Connection": "keep-alive"
}
manual_cookies = {}


def get_tag_value(tag, key='', index=0):
    if key:
        value = tag[index].get(key)
    else:
        value = tag[index].text
    return value.strip(' \t\r\n')


def response_status(resp):
    if resp.status_code != requests.codes.OK:
        print('Status: %u, Url: %s' % (resp.status_code, resp.url))
        return False
    return True


for item in cookies_String.split(';'):
    name, value = item.strip().split('=', 1)
    # 用=号分割，分割1次
    manual_cookies[name] = value
    # 为字典cookies添加内容

cookiesJar = requests.utils.cookiejar_from_dict(manual_cookies, cookiejar=None, overwrite=True)
session.cookies = cookiesJar


def validate_cookies():
    for flag in range(1, 3):
        try:
            targetURL = 'https://order.jd.com/center/list.action'
            payload = {
                'rid': str(int(time.time() * 1000)),
            }
            resp = session.get(url=targetURL, params=payload, allow_redirects=False)
            if resp.status_code == requests.codes.OK:
                logger.info('登录成功')
                return True
            else:
                logger.info('第【%s】次请重新获取cookie', flag)
                sendMail(mail, '需要重新登录', True)
                time.sleep(5)
                continue
        except Exception as e:
            logger.info('第【%s】次请重新获取cookie', flag)
            time.sleep(5)
            continue


def getUsername():
    userName_Url = 'https://passport.jd.com/new/helloService.ashx?callback=jQuery339448&_=' + str(
        int(time.time() * 1000))
    session.headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
        "Referer": "https://order.jd.com/center/list.action",
        "Connection": "keep-alive"
    }
    resp = session.get(url=userName_Url, allow_redirects=True)
    resultText = resp.text
    resultText = resultText.replace('jQuery339448(', '')
    resultText = resultText.replace(')', '')
    usernameJson = json.loads(resultText)
    logger.info('登录账号名称' + usernameJson['nick'])


'''
检查是否有货
'''


def check_item_stock(itemUrl):
    response = session.get(itemUrl)
    if (response.text.find('无货') > 0):
        return True
    else:
        return False


'''
取消勾选购物车中的所有商品
'''


def cancel_select_all_cart_item():
    url = "https://cart.jd.com/cancelAllItem.action"
    data = {
        't': 0,
        'outSkus': '',
        'random': random.random()
    }
    resp = session.post(url, data=data)
    if resp.status_code != requests.codes.OK:
        print('Status: %u, Url: %s' % (resp.status_code, resp.url))
        return False
    return True


'''
购物车详情
'''


def cart_detail():
    url = 'https://cart.jd.com/cart.action'
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
        "Referer": "https://order.jd.com/center/list.action",
        "Host": "cart.jd.com",
        "Connection": "keep-alive"
    }
    resp = session.get(url, headers=headers)
    soup = BeautifulSoup(resp.text, "html.parser")

    cart_detail = dict()
    for item in soup.find_all(class_='item-item'):
        try:
            sku_id = item['skuid']  # 商品id
        except Exception as e:
            logger.info('购物车中有套装商品，跳过')
            continue
        try:
            # 例如：['increment', '8888', '100001071956', '1', '13', '0', '50067652554']
            # ['increment', '8888', '100002404322', '2', '1', '0']
            item_attr_list = item.find(class_='increment')['id'].split('_')
            p_type = item_attr_list[4]
            promo_id = target_id = item_attr_list[-1] if len(item_attr_list) == 7 else 0

            cart_detail[sku_id] = {
                'name': get_tag_value(item.select('div.p-name a')),  # 商品名称
                'verder_id': item['venderid'],  # 商家id
                'count': int(item['num']),  # 数量
                'unit_price': get_tag_value(item.select('div.p-price strong'))[1:],  # 单价
                'total_price': get_tag_value(item.select('div.p-sum strong'))[1:],  # 总价
                'is_selected': 'item-selected' in item['class'],  # 商品是否被勾选
                'p_type': p_type,
                'target_id': target_id,
                'promo_id': promo_id
            }
        except Exception as e:
            logger.error("商品%s在购物车中的信息无法解析，报错信息: %s，该商品自动忽略", sku_id, e)

    logger.info('购物车信息：%s', cart_detail)
    return cart_detail


'''
修改购物车商品的数量
'''


def change_item_num_in_cart(sku_id, vender_id, num, p_type, target_id, promo_id):
    url = "https://cart.jd.com/changeNum.action"
    data = {
        't': 0,
        'venderId': vender_id,
        'pid': sku_id,
        'pcount': num,
        'ptype': p_type,
        'targetId': target_id,
        'promoID': promo_id,
        'outSkus': '',
        'random': random.random(),
        # 'locationId'
    }
    session.headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
        "Referer": "https://cart.jd.com/cart",
        "Connection": "keep-alive"
    }
    resp = session.post(url, data=data)
    return json.loads(resp.text)['sortedWebCartResult']['achieveSevenState'] == 2


'''
添加商品到购物车
'''


def add_item_to_cart(sku_id):
    url = 'https://cart.jd.com/gate.action'
    payload = {
        'pid': sku_id,
        'pcount': 1,
        'ptype': 1,
    }
    resp = session.get(url=url, params=payload)
    if 'https://cart.jd.com/cart.action' in resp.url:  # 套装商品加入购物车后直接跳转到购物车页面
        result = True
    else:  # 普通商品成功加入购物车后会跳转到提示 "商品已成功加入购物车！" 页面
        soup = BeautifulSoup(resp.text, "html.parser")
        result = bool(soup.select('h3.ftx-02'))  # [<h3 class="ftx-02">商品已成功加入购物车！</h3>]

    if result:
        logger.info('%s  已成功加入购物车', sku_id)
    else:
        logger.error('%s 添加到购物车失败', sku_id)


def get_checkout_page_detail():
    """获取订单结算页面信息

    该方法会返回订单结算页面的详细信息：商品名称、价格、数量、库存状态等。

    :return: 结算信息 dict
    """
    url = 'http://trade.jd.com/shopping/order/getOrderInfo.action'
    # url = 'https://cart.jd.com/gotoOrder.action'
    payload = {
        'rid': str(int(time.time() * 1000)),
    }
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
        "Referer": "https://cart.jd.com/cart.action",
        "Connection": "keep-alive",
        'Host': 'trade.jd.com',
    }
    try:
        resp = session.get(url=url, params=payload, headers=headers)
        if not response_status(resp):
            logger.error('获取订单结算页信息失败')
            return ''

        soup = BeautifulSoup(resp.text, "html.parser")
        risk_control = get_tag_value(soup.select('input#riskControl'), 'value')

        order_detail = {
            'address': soup.find('span', id='sendAddr').text[5:],  # remove '寄送至： ' from the begin
            'receiver': soup.find('span', id='sendMobile').text[4:],  # remove '收件人:' from the begin
            'total_price': soup.find('span', id='sumPayPriceId').text[1:],  # remove '￥' from the begin
            'items': []
        }

        logger.info("下单信息：%s", order_detail)
        return order_detail
    except requests.exceptions.RequestException as e:
        logger.error('订单结算页面获取异常：%s' % e)
    except Exception as e:
        logger.error('下单页面数据解析异常：%s', e)
    return risk_control


def submit_order(risk_control):
    """提交订单

    重要：
    1.该方法只适用于普通商品的提交订单（即可以加入购物车，然后结算提交订单的商品）
    2.提交订单时，会对购物车中勾选✓的商品进行结算（如果勾选了多个商品，将会提交成一个订单）

    :return: True/False 订单提交结果
    """
    url = 'https://trade.jd.com/shopping/order/submitOrder.action'
    # js function of submit order is included in https://trade.jd.com/shopping/misc/js/order.js?r=2018070403091

    # overseaPurchaseCookies:
    # vendorRemarks: []
    # submitOrderParam.sopNotPutInvoice: false
    # submitOrderParam.trackID: TestTrackId
    # submitOrderParam.ignorePriceChange: 0
    # submitOrderParam.btSupport: 0
    # riskControl:
    # submitOrderParam.isBestCoupon: 1
    # submitOrderParam.jxj: 1
    # submitOrderParam.trackId:

    data = {
        'overseaPurchaseCookies': '',
        'vendorRemarks': '[]',
        'submitOrderParam.sopNotPutInvoice': 'false',
        'submitOrderParam.trackID': 'TestTrackId',
        'submitOrderParam.ignorePriceChange': '0',
        'submitOrderParam.btSupport': '0',
        'riskControl': risk_control,
        'submitOrderParam.isBestCoupon': 1,
        'submitOrderParam.jxj': 1,
        'submitOrderParam.trackId': '9643cbd55bbbe103eef18a213e069eb0',  # Todo: need to get trackId
        # 'submitOrderParam.eid': eid,
        # 'submitOrderParam.fp': fp,
        'submitOrderParam.needCheck': 1,
    }

    def encrypt_payment_pwd(payment_pwd):
        return ''.join(['u3' + x for x in payment_pwd])

    if len(payment_pwd) > 0:
        data['submitOrderParam.payPassword'] = encrypt_payment_pwd(payment_pwd)

    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
        "Referer": "http://trade.jd.com/shopping/order/getOrderInfo.action",
        "Connection": "keep-alive",
        'Host': 'trade.jd.com',
    }

    try:
        resp = session.post(url=url, data=data, headers=headers)
        resp_json = json.loads(resp.text)

        # 返回信息示例：
        # 下单失败
        # {'overSea': False, 'orderXml': None, 'cartXml': None, 'noStockSkuIds': '', 'reqInfo': None, 'hasJxj': False, 'addedServiceList': None, 'sign': None, 'pin': 'xxx', 'needCheckCode': False, 'success': False, 'resultCode': 60123, 'orderId': 0, 'submitSkuNum': 0, 'deductMoneyFlag': 0, 'goJumpOrderCenter': False, 'payInfo': None, 'scaleSkuInfoListVO': None, 'purchaseSkuInfoListVO': None, 'noSupportHomeServiceSkuList': None, 'msgMobile': None, 'addressVO': None, 'msgUuid': None, 'message': '请输入支付密码！'}
        # {'overSea': False, 'cartXml': None, 'noStockSkuIds': '', 'reqInfo': None, 'hasJxj': False, 'addedServiceList': None, 'orderXml': None, 'sign': None, 'pin': 'xxx', 'needCheckCode': False, 'success': False, 'resultCode': 60017, 'orderId': 0, 'submitSkuNum': 0, 'deductMoneyFlag': 0, 'goJumpOrderCenter': False, 'payInfo': None, 'scaleSkuInfoListVO': None, 'purchaseSkuInfoListVO': None, 'noSupportHomeServiceSkuList': None, 'msgMobile': None, 'addressVO': None, 'msgUuid': None, 'message': '您多次提交过快，请稍后再试'}
        # {'overSea': False, 'orderXml': None, 'cartXml': None, 'noStockSkuIds': '', 'reqInfo': None, 'hasJxj': False, 'addedServiceList': None, 'sign': None, 'pin': 'xxx', 'needCheckCode': False, 'success': False, 'resultCode': 60077, 'orderId': 0, 'submitSkuNum': 0, 'deductMoneyFlag': 0, 'goJumpOrderCenter': False, 'payInfo': None, 'scaleSkuInfoListVO': None, 'purchaseSkuInfoListVO': None, 'noSupportHomeServiceSkuList': None, 'msgMobile': None, 'addressVO': None, 'msgUuid': None, 'message': '获取用户订单信息失败'}
        # {"cartXml":null,"noStockSkuIds":"xxx","reqInfo":null,"hasJxj":false,"addedServiceList":null,"overSea":false,"orderXml":null,"sign":null,"pin":"xxx","needCheckCode":false,"success":false,"resultCode":600157,"orderId":0,"submitSkuNum":0,"deductMoneyFlag":0,"goJumpOrderCenter":false,"payInfo":null,"scaleSkuInfoListVO":null,"purchaseSkuInfoListVO":null,"noSupportHomeServiceSkuList":null,"msgMobile":null,"addressVO":{"pin":"xxx","areaName":"","provinceId":xx,"cityId":xx,"countyId":xx,"townId":xx,"paymentId":0,"selected":false,"addressDetail":"xx","mobile":"xx","idCard":"","phone":null,"email":null,"selfPickMobile":null,"selfPickPhone":null,"provinceName":null,"cityName":null,"countyName":null,"townName":null,"giftSenderConsigneeName":null,"giftSenderConsigneeMobile":null,"gcLat":0.0,"gcLng":0.0,"coord_type":0,"longitude":0.0,"latitude":0.0,"selfPickOptimize":0,"consigneeId":0,"selectedAddressType":0,"siteType":0,"helpMessage":null,"tipInfo":null,"cabinetAvailable":true,"limitKeyword":0,"specialRemark":null,"siteProvinceId":0,"siteCityId":0,"siteCountyId":0,"siteTownId":0,"skuSupported":false,"addressSupported":0,"isCod":0,"consigneeName":null,"pickVOname":null,"shipmentType":0,"retTag":0,"tagSource":0,"userDefinedTag":null,"newProvinceId":0,"newCityId":0,"newCountyId":0,"newTownId":0,"newProvinceName":null,"newCityName":null,"newCountyName":null,"newTownName":null,"checkLevel":0,"optimizePickID":0,"pickType":0,"dataSign":0,"overseas":0,"areaCode":null,"nameCode":null,"appSelfPickAddress":0,"associatePickId":0,"associateAddressId":0,"appId":null,"encryptText":null,"certNum":null,"used":false,"oldAddress":false,"mapping":false,"addressType":0,"fullAddress":"xxxx","postCode":null,"addressDefault":false,"addressName":null,"selfPickAddressShuntFlag":0,"pickId":0,"pickName":null,"pickVOselected":false,"mapUrl":null,"branchId":0,"canSelected":false,"address":null,"name":"xxx","message":null,"id":0},"msgUuid":null,"message":"xxxxxx商品无货"}
        # {'orderXml': None, 'overSea': False, 'noStockSkuIds': 'xxx', 'reqInfo': None, 'hasJxj': False, 'addedServiceList': None, 'cartXml': None, 'sign': None, 'pin': 'xxx', 'needCheckCode': False, 'success': False, 'resultCode': 600158, 'orderId': 0, 'submitSkuNum': 0, 'deductMoneyFlag': 0, 'goJumpOrderCenter': False, 'payInfo': None, 'scaleSkuInfoListVO': None, 'purchaseSkuInfoListVO': None, 'noSupportHomeServiceSkuList': None, 'msgMobile': None, 'addressVO': {'oldAddress': False, 'mapping': False, 'pin': 'xxx', 'areaName': '', 'provinceId': xx, 'cityId': xx, 'countyId': xx, 'townId': xx, 'paymentId': 0, 'selected': False, 'addressDetail': 'xxxx', 'mobile': 'xxxx', 'idCard': '', 'phone': None, 'email': None, 'selfPickMobile': None, 'selfPickPhone': None, 'provinceName': None, 'cityName': None, 'countyName': None, 'townName': None, 'giftSenderConsigneeName': None, 'giftSenderConsigneeMobile': None, 'gcLat': 0.0, 'gcLng': 0.0, 'coord_type': 0, 'longitude': 0.0, 'latitude': 0.0, 'selfPickOptimize': 0, 'consigneeId': 0, 'selectedAddressType': 0, 'newCityName': None, 'newCountyName': None, 'newTownName': None, 'checkLevel': 0, 'optimizePickID': 0, 'pickType': 0, 'dataSign': 0, 'overseas': 0, 'areaCode': None, 'nameCode': None, 'appSelfPickAddress': 0, 'associatePickId': 0, 'associateAddressId': 0, 'appId': None, 'encryptText': None, 'certNum': None, 'addressType': 0, 'fullAddress': 'xxxx', 'postCode': None, 'addressDefault': False, 'addressName': None, 'selfPickAddressShuntFlag': 0, 'pickId': 0, 'pickName': None, 'pickVOselected': False, 'mapUrl': None, 'branchId': 0, 'canSelected': False, 'siteType': 0, 'helpMessage': None, 'tipInfo': None, 'cabinetAvailable': True, 'limitKeyword': 0, 'specialRemark': None, 'siteProvinceId': 0, 'siteCityId': 0, 'siteCountyId': 0, 'siteTownId': 0, 'skuSupported': False, 'addressSupported': 0, 'isCod': 0, 'consigneeName': None, 'pickVOname': None, 'shipmentType': 0, 'retTag': 0, 'tagSource': 0, 'userDefinedTag': None, 'newProvinceId': 0, 'newCityId': 0, 'newCountyId': 0, 'newTownId': 0, 'newProvinceName': None, 'used': False, 'address': None, 'name': 'xx', 'message': None, 'id': 0}, 'msgUuid': None, 'message': 'xxxxxx商品无货'}
        # 下单成功
        # {'overSea': False, 'orderXml': None, 'cartXml': None, 'noStockSkuIds': '', 'reqInfo': None, 'hasJxj': False, 'addedServiceList': None, 'sign': None, 'pin': 'xxx', 'needCheckCode': False, 'success': True, 'resultCode': 0, 'orderId': 8740xxxxx, 'submitSkuNum': 1, 'deductMoneyFlag': 0, 'goJumpOrderCenter': False, 'payInfo': None, 'scaleSkuInfoListVO': None, 'purchaseSkuInfoListVO': None, 'noSupportHomeServiceSkuList': None, 'msgMobile': None, 'addressVO': None, 'msgUuid': None, 'message': None}

        if resp_json.get('success'):
            logger.info('订单提交成功! 订单号：%s', resp_json.get('orderId'))
            return True
        else:
            message, result_code = resp_json.get('message'), resp_json.get('resultCode')
            if result_code == 0:
                # self._save_invoice()
                message = message + '(下单商品可能为第三方商品，将切换为普通发票进行尝试)'
            elif result_code == 60077:
                message = message + '(可能是购物车为空 或 未勾选购物车中商品)'
            elif result_code == 60123:
                message = message + '(需要在payment_pwd参数配置支付密码)'
            logger.info('订单提交失败, 错误码：%s, 返回信息：%s', result_code, message)
            logger.info(resp_json)
            return False
    except Exception as e:
        logger.error(e)
        return False


'''

'''


def item_removed(sku_id):
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
        "Referer": "http://trade.jd.com/shopping/order/getOrderInfo.action",
        "Connection": "keep-alive",
        'Host': 'item.jd.com',
    }
    url = 'https://item.jd.com/{}.html'.format(sku_id)
    page = requests.get(url=url, headers=headers)
    return '该商品已下柜' not in page.text


'''
购买环节
测试三次
'''


def buyMask(sku_id):
    for count in range(1, 2):
        logger.info('第[%s/%s]次尝试提交订单', count, 3)
        cancel_select_all_cart_item()
        cart = cart_detail()
        if sku_id in cart:
            logger.info('%s 已在购物车中，调整数量为 %s', sku_id, 1)
            cart_item = cart.get(sku_id)
            change_item_num_in_cart(
                sku_id=sku_id,
                vender_id=cart_item.get('vender_id'),
                num=1,
                p_type=cart_item.get('p_type'),
                target_id=cart_item.get('target_id'),
                promo_id=cart_item.get('promo_id')
            )
        else:
            add_item_to_cart(sku_id)
        risk_control = get_checkout_page_detail()
        if len(risk_control) > 0:
            if submit_order(risk_control):
                return True
        logger.info('休息%ss', 3)
        time.sleep(3)
    else:
        logger.info('执行结束，提交订单失败！')
        return False


flag = 1
while (1):
    try:
        if flag == 1:
            validate_cookies()
            getUsername()
        checkSession = requests.Session()
        checkSession.headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/75.0.3770.100 Safari/531.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3",
            "Connection": "keep-alive"
        }
        logger.info('第' + str(flag) + '次 ')
        flag += 1
        for i in url:
            # 商品url
            skuId = i.split('skuId=')[1].split('&')[0]
            skuidUrl = 'https://item.jd.com/' + skuId + '.html'
            response = checkSession.get(i)
            if (response.text.find('无货') > 0):
                logger.info('[%s]类型口罩无货', skuId)
            else:
                if item_removed(skuId):
                    logger.info('[%s]类型口罩有货啦!马上下单', skuId)
                    if buyMask(skuId):
                        sendMail(mail, skuidUrl, True)
                    else:
                        sendMail(mail, skuidUrl, False)
                else:
                    logger.info('[%s]类型口罩有货，但已下柜商品', skuId)
        time.sleep(timesleep)
        if flag % 20 == 0:
            logger.info('校验是否还在登录')
            validate_cookies()
    except Exception as e:
        import traceback

        print(traceback.format_exc())
        time.sleep(10)
